# SỔ VẬN HÀNH — đọc file này trước tiên nếu bạn là session mới

Đây là tài liệu bàn giao. Session trước có thể đã bị xóa ngữ cảnh; mọi thứ cần
để tiếp tục nằm ở đây, không nằm trong đầu ai.

## 1. Mốc thời gian (KHÔNG THƯƠNG LƯỢNG)

| Mốc | Thời điểm |
|---|---|
| Chủ dự án bay khỏi Việt Nam | **đêm 26/08/2026** |
| Ổn định lại ở Mỹ | tối 27/08 giờ Mỹ |
| Hạn nộp | 31/08 23:59 AoE = **01/09 04:59 PDT / 07:59 EDT / 18:59 giờ VN** |
| **ĐÓNG BĂNG + NỘP BẢN CHẮC** | **26/08 12:00 giờ VN** — trước khi ra sân bay |

Cửa sổ làm việc bị chia đôi bởi chuyến bay. Trong quãng bay máy có thể tắt —
dây chuyền tự chạy lại được, xem mục 3.

## 2. Trạng thái ngay lúc này

Chạy lệnh này, đừng đoán:

```bash
bash .scratch/release/run_chain.sh status
```

Sổ nhật ký: `$SCRATCH/chain.log`. Kết quả từng chặng nằm trong `$SCRATCH/` và
`.scratch/ml/`, `.scratch/frontier-forge/`.

Điểm chuẩn đã chứng nhận: **2.434/2.469** (sweep chính chủ, không LLM). Đã đòi
lại thêm **26 bài** trong ngày 20/08, mỗi bài có dấu judge riêng, nên trần lý
thuyết là **2.460**. Đối thủ mạnh nhất (reja23): 2.411.

## 3. Tự động hóa — đã cài, không cần nhớ gì

Dịch vụ `com.magmaballz.chain` (LaunchAgent) chạy khi đăng nhập và mỗi 10 phút.
Nó gọi `run_chain.sh`, script này bỏ qua chặng đã xong và tiếp chặng dở.

```bash
launchctl list | grep magmaballz     # còn sống không
launchctl unload ~/Library/LaunchAgents/com.magmaballz.chain.plist   # gỡ khi xong
```

Chặng: verify → Marathon → sweep chứng nhận → sieve Forge → harvest ML →
census route → label_doubt.

## 4. Nguyên tắc vận hành — vi phạm là trả giá bằng số liệu sai

1. **Không đo và không đánh cùng lúc.** Tải máy đã từng làm lệch một sweep +4
   rồi −18 bài. Mọi phép đo chạy tuần tự qua dây chuyền.
2. **Mọi thay đổi engine là CỘNG THÊM, không thay thế** — trừ khi chứng minh
   được tương đương từng bổ đề. Một lần thay thế đã lấy 3 bài và mất 3 bài.
3. **Không tính điểm cho bài nào chưa có dấu judge.**
4. **Build cho sweep ghim theo commit**, không bao giờ chép file đang sửa.
5. **Không tin mã thoát — chỉ tin dấu hoàn thành do công việc tự ghi ra.**
   Trong một ngày đã có NĂM lỗi cùng họ "chạy mà không làm gì, trông như đang
   làm": build ghim cũ, thiếu `cd`, đường dẫn `.env.judge`, `xcodebuild` treo
   dưới launchd, `python3` phân giải sai dưới launchd.
6. **Nhãn trong corpus KHÔNG đáng tin** (người đóng góp tự gán). Judge chấm
   theo chứng minh, không theo nhãn. Đừng để nhãn ngăn mình thử hướng ngược lại.

## 5. Khung bốn cần gạt — dùng để quyết định đầu tư

| Cần gạt | Câu hỏi | Ghi chú |
|---|---|---|
| **TẦM VỚI** | Lời giải có nằm trong không gian mình quét không? | **Cổng chặn**, không phải hệ số nhân. Thu hoạch lớn nhất hôm nay đến từ đây (14 bài). |
| **ĐỔI BÀI** | Có đích dễ hơn mà lời giải chuyển được không? | heavy-ladder, máy vét cầu (7 bài). |
| **THỨ TỰ** | Trong tầm với, gặp thứ đúng trước hay sau? | Nơi ML/heuristic sống. **Chỉ xếp hạng, KHÔNG BAO GIỜ cắt bỏ.** |
| **TỐC ĐỘ** | Bao nhiêu nút mỗi giây? | Tìm kiếm hai chiều: 231×. |

Chẩn đoán đã rút ra: *một cái nắp trở thành đóng băng khi tập nó cắt bớt vừa
tăng đơn điệu vừa xếp theo thứ tự chèn vào.*

## 6. Vì sao vẫn làm Forge và ML dù dư địa chỉ 9 bài

Vì dư địa 9 bài là **có điều kiện** vào việc bộ đề riêng cùng độ khó với corpus
công khai. Nếu nó khó hơn:

| Bộ đề riêng giống… | Điểm dự phóng |
|---|---|
| `normal` | 2.469 |
| `hard2` | 2.432 |
| `evaluation_order5` | **2.407** |

Rủi ro dịch phân bố (−53) lớn gấp ~6 lần dư địa (+9). Forge và ML là **bảo
hiểm**, không phải phần thưởng. Ưu tiên chế đề: order-5 trước, rồi hard2.

## 7. Việc còn lại, theo thứ tự

**Chặn nộp bài:** xác nhận đội đã đăng ký trên nền tảng; xem form nộp đòi gì;
kiểm tra có cho nộp đè không (nếu có → nộp bản chắc NGAY, cải tiến sau).

**Bảo vệ điểm:** mở rộng đồng hồ công ra các tầng còn cắt theo giây; chốt chặn
ngân sách Marathon; Docker dựng lại với build cuối.

**Ăn thêm bài:** lane model vô hạn (luật cho phép **inductive tự định nghĩa**,
xem commit upstream `40b7d56`); bộ tìm model hữu hạn bậc 13–30; cắt tầng bị
thâu tóm sau khi có census.

**Bảo hiểm:** Forge đầy đủ (không bản thu gọn) + ML (harvest → phép thử tuyến
tính → GBDT nếu thắng → nhúng vào khóa sắp xếp).

## 8. Gói nộp

```bash
bash .scratch/release/make_submission.sh          # từ HEAD
bash .scratch/release/make_submission.sh <commit>
```
Xuất `.scratch/release/submission/` và **từ chối xuất nếu vi phạm bất kỳ ràng
buộc nào** (>500KB, sai cú pháp, thiếu `PROMPT`, import ngoài thư viện chuẩn).
Ghi chú công bố phương pháp bắt buộc phải nộp kèm — kho witness là dữ liệu sinh
ra, luật đòi công bố.

## 9. Tài liệu tham chiếu

- `SOLVER_DOCS.md` — tham chiếu từng hàm của solver, **đọc trước khi sửa**
- `SUBMISSION_NOTE.md` — ghi chú công bố, nộp kèm
- `.scratch/frontier-forge/plan.md` — kế hoạch Forge + 4 phụ lục
- `.scratch/release/RESUME.md` — cách khởi động lại sau khi máy tắt
