//! ESP32 no_std: quét Wi-Fi mỗi 15', lưu flash (kèm thời gian), về nhà thì upload.
//!
//! Lưu ý: API esp-radio / esp-hal đổi khá nhanh. Những dòng có `// CHECK` là chỗ
//! hay lệch giữa các phiên bản -> tạo project bằng `esp-generate` rồi đối chiếu.
#![no_std]
#![no_main]

extern crate alloc;

use alloc::string::String;
use core::fmt::Write as _;
use core::time::Duration;

use embassy_executor::Spawner;
use embassy_net::{dns::DnsSocket, tcp::client::{TcpClient, TcpClientState}, StackResources};
use embassy_time::{Duration as EDuration, Timer};
use embedded_storage::nor_flash::{NorFlash, ReadNorFlash};
use esp_backtrace as _;
use esp_hal::{
    clock::CpuClock,
    rtc_cntl::{sleep::TimerWakeupSource, Rtc},
    timer::timg::TimerGroup,
};
use esp_radio::wifi::{ClientConfig, ModeConfig, ScanConfig, WifiController};
use esp_storage::FlashStorage;
use reqwless::{client::HttpClient, headers::ContentType, request::{Method, RequestBuilder}};
use static_cell::StaticCell;

esp_bootloader_esp_idf::esp_app_desc!();

// ====== CẤU HÌNH ======
const HOME_SSID: &str = "WIFI_NHA";
const HOME_PASS: &str = "matkhau";
const API_URL: &str = "http://api.example.com/locate"; // HTTPS cần thêm esp-mbedtls
const SCAN_INTERVAL_S: u64 = 15 * 60;
const MAX_AP: usize = 12;

// Vùng flash dành cho log (khai báo trong partitions.csv, offset phải khớp)
const LOG_OFFSET: u32 = 0x0031_0000;
const SECTOR: u32 = 4096;
const SECTORS: u32 = 64; // 256 KB ≈ 2048 record ≈ 21 ngày
const REC_SIZE: u32 = 128;
const SLOTS_PER_SECTOR: u32 = SECTOR / REC_SIZE;
const SLOTS: u32 = SECTORS * SLOTS_PER_SECTOR;
const MAGIC: u16 = 0xA55A;

// ====== RECORD TRONG FLASH (128 byte) ======
// 0..2 magic | 2 count | 4..8 seq | 8..12 rtc_s | 12.. AP (bssid6 + rssi1 + ch1) * MAX_AP
#[derive(Clone, Copy)]
struct Ap {
    bssid: [u8; 6],
    rssi: i8,
    ch: u8,
}

struct Record {
    seq: u32,
    rtc_s: u32, // giây theo đồng hồ RTC (sống qua deep sleep, mất khi cúp nguồn)
    count: u8,
    aps: [Ap; MAX_AP],
}

fn encode(r: &Record) -> [u8; REC_SIZE as usize] {
    let mut b = [0xFFu8; REC_SIZE as usize];
    b[0..2].copy_from_slice(&MAGIC.to_le_bytes());
    b[2] = r.count;
    b[4..8].copy_from_slice(&r.seq.to_le_bytes());
    b[8..12].copy_from_slice(&r.rtc_s.to_le_bytes());
    for (i, ap) in r.aps.iter().take(r.count as usize).enumerate() {
        let o = 12 + i * 8;
        b[o..o + 6].copy_from_slice(&ap.bssid);
        b[o + 6] = ap.rssi as u8;
        b[o + 7] = ap.ch;
    }
    b
}

fn decode(b: &[u8; REC_SIZE as usize]) -> Option<Record> {
    if u16::from_le_bytes([b[0], b[1]]) != MAGIC {
        return None;
    }
    let count = (b[2] as usize).min(MAX_AP);
    let mut aps = [Ap { bssid: [0; 6], rssi: 0, ch: 0 }; MAX_AP];
    for i in 0..count {
        let o = 12 + i * 8;
        aps[i] = Ap { bssid: b[o..o + 6].try_into().unwrap(), rssi: b[o + 6] as i8, ch: b[o + 7] };
    }
    Some(Record {
        seq: u32::from_le_bytes(b[4..8].try_into().unwrap()),
        rtc_s: u32::from_le_bytes(b[8..12].try_into().unwrap()),
        count: count as u8,
        aps,
    })
}

// ====== LOG DẠNG VÒNG TRÊN FLASH ======
struct Log<'a> {
    flash: FlashStorage<'a>,
}

impl<'a> Log<'a> {
    fn read_slot(&mut self, slot: u32) -> Option<Record> {
        let mut buf = [0u8; REC_SIZE as usize];
        self.flash.read(LOG_OFFSET + slot * REC_SIZE, &mut buf).ok()?;
        decode(&buf)
    }

    /// Trả về (slot đầu ghi tiếp theo, seq tiếp theo): slot đứng sau record có seq lớn nhất.
    fn head(&mut self) -> (u32, u32) {
        let mut best: Option<(u32, u32)> = None; // (seq, slot)
        for s in 0..SLOTS {
            if let Some(r) = self.read_slot(s) {
                if best.map_or(true, |(bs, _)| r.seq > bs) {
                    best = Some((r.seq, s));
                }
            }
        }
        match best {
            Some((seq, slot)) => ((slot + 1) % SLOTS, seq + 1),
            None => (0, 0),
        }
    }

    fn append(&mut self, mut rec: Record) {
        let (slot, seq) = self.head();
        rec.seq = seq;
        let off = LOG_OFFSET + slot * REC_SIZE;
        // Vào sector mới -> xoá nó trước (ghi đè sector cũ nhất, kiểu ring buffer)
        if slot % SLOTS_PER_SECTOR == 0 {
            let _ = self.flash.erase(off, off + SECTOR);
        }
        let _ = self.flash.write(off, &encode(&rec));
    }

    fn erase_all(&mut self) {
        let _ = self.flash.erase(LOG_OFFSET, LOG_OFFSET + SECTORS * SECTOR);
    }
}

// ====== QUÉT WI-FI ======
async fn scan(controller: &mut WifiController<'_>, rtc_s: u32) -> (Record, bool) {
    let mut rec = Record { seq: 0, rtc_s, count: 0, aps: [Ap { bssid: [0; 6], rssi: 0, ch: 0 }; MAX_AP] };
    let mut at_home = false;
    if let Ok(list) = controller.scan_with_config_async(ScanConfig::default().with_max(20)).await {
        // list đã sắp theo RSSI giảm dần -> giữ MAX_AP cái mạnh nhất
        for ap in list.iter() {
            if ap.ssid.as_str() == HOME_SSID {
                at_home = true;
            }
            // Lọc: AP quá yếu, SSID _nomap, hotspot di động (MAC locally-administered)
            let s = ap.ssid.as_str();
            if ap.signal_strength < -90 || s.ends_with("_nomap") || (ap.bssid[0] & 0x02) != 0 {
                continue;
            }
            if (rec.count as usize) < MAX_AP {
                rec.aps[rec.count as usize] =
                    Ap { bssid: ap.bssid, rssi: ap.signal_strength, ch: ap.channel };
                rec.count += 1;
            }
        }
    }
    (rec, at_home)
}

// ====== UPLOAD ======
/// Mỗi record gửi 1 POST. Server dựng lại thời điểm thật:
///   t_upload = lúc nhận request;  t_scan = t_upload - age_s
///   hoặc cộng dồn ngược bằng dt_prev_s (dùng được cả khi RTC bị reset).
async fn upload(
    log: &mut Log<'_>,
    stack: embassy_net::Stack<'static>,
    now_s: u32,
) -> bool {
    static STATE: StaticCell<TcpClientState<1, 1024, 1024>> = StaticCell::new();
    let state = STATE.init(TcpClientState::new());
    let tcp = TcpClient::new(stack, state);
    let dns = DnsSocket::new(stack);
    let mut client = HttpClient::new(&tcp, &dns);

    let mut prev: Option<u32> = None;
    let (start, _) = log.head(); // slot sau head = bản ghi cũ nhất
    let mut sent_any = false;
    let mut rx = [0u8; 512];

    for i in 0..SLOTS {
        let slot = (start + i) % SLOTS;
        let Some(r) = log.read_slot(slot) else { continue };

        let mut body = String::new();
        let dt_prev = prev.map(|p| r.rtc_s.wrapping_sub(p)); // None với record đầu tiên
        let age = now_s.checked_sub(r.rtc_s); // None nếu RTC đã reset
        let _ = write!(body, "{{\"seq\":{},\"dt_prev_s\":", r.seq);
        match dt_prev { Some(v) => { let _ = write!(body, "{v}"); } None => body.push_str("null") }
        body.push_str(",\"age_s\":");
        match age { Some(v) => { let _ = write!(body, "{v}"); } None => body.push_str("null") }
        body.push_str(",\"aps\":[");
        for (k, ap) in r.aps.iter().take(r.count as usize).enumerate() {
            if k > 0 { body.push(','); }
            let b = ap.bssid;
            let _ = write!(
                body,
                "{{\"bssid\":\"{:02X}:{:02X}:{:02X}:{:02X}:{:02X}:{:02X}\",\"rssi\":{},\"ch\":{}}}",
                b[0], b[1], b[2], b[3], b[4], b[5], ap.rssi, ap.ch
            );
        }
        body.push_str("]}");

        let ok = async {
            let mut req = client.request(Method::POST, API_URL).await.ok()?
                .content_type(ContentType::ApplicationJson)
                .body(body.as_bytes());
            let resp = req.send(&mut rx).await.ok()?;
            resp.status.is_successful().then_some(())
        }.await;

        if ok.is_none() {
            return false; // giữ nguyên log, lần sau gửi lại
        }
        prev = Some(r.rtc_s);
        sent_any = true;
    }
    if sent_any {
        log.erase_all();
    }
    true
}

macro_rules! mk_static {
    ($t:ty, $val:expr) => {{
        static C: StaticCell<$t> = StaticCell::new();
        C.uninit().write($val)
    }};
}

#[esp_rtos::main] // CHECK: tên macro/attr tuỳ version (esp_rtos::main hoặc esp_hal_embassy::main)
async fn main(spawner: Spawner) -> ! {
    let p = esp_hal::init(esp_hal::Config::default().with_cpu_clock(CpuClock::max()));
    esp_alloc::heap_allocator!(size: 72 * 1024);

    let timg0 = TimerGroup::new(p.TIMG0);
    esp_rtos::start(timg0.timer0); // CHECK

    let mut rtc = Rtc::new(p.LPWR);
    let now_s = (rtc.current_time_us() / 1_000_000) as u32;

    let radio = mk_static!(esp_radio::Controller<'static>, esp_radio::init().unwrap());
    let (mut controller, ifaces) =
        esp_radio::wifi::new(radio, p.WIFI, Default::default()).unwrap(); // CHECK
    controller.set_config(&ModeConfig::Client(ClientConfig::default())).unwrap();
    controller.start_async().await.unwrap();

    let mut log = Log { flash: FlashStorage::new(p.FLASH) };

    // 1) Quét + lưu flash
    let (rec, at_home) = scan(&mut controller, now_s).await;
    log.append(rec);

    // 2) Thấy Wi-Fi nhà -> kết nối + upload
    if at_home {
        controller
            .set_config(&ModeConfig::Client(
                ClientConfig::default().with_ssid(HOME_SSID.into()).with_password(HOME_PASS.into()),
            ))
            .unwrap();
        if controller.connect_async().await.is_ok() {
            let rng = esp_hal::rng::Rng::new();
            let seed = (rng.random() as u64) << 32 | rng.random() as u64;
            let (stack, mut runner) = embassy_net::new(
                ifaces.sta,
                embassy_net::Config::dhcpv4(Default::default()),
                mk_static!(StackResources<4>, StackResources::<4>::new()),
                seed,
            );
            // Chạy network runner song song với upload
            let net = runner.run();
            let work = async {
                stack.wait_config_up().await;
                Timer::after(EDuration::from_millis(300)).await;
                let now = (rtc.current_time_us() / 1_000_000) as u32;
                upload(&mut log, stack, now).await
            };
            let _ = embassy_futures::select::select(net, work).await;
        }
    }
    let _ = spawner;

    // 3) Ngủ sâu 15'
    let wake = TimerWakeupSource::new(Duration::from_secs(SCAN_INTERVAL_S));
    rtc.sleep_deep(&[&wake]);
}
