# TRẠNG THÁI — tự sinh lúc 2026-08-26 11:32

Sinh bởi `.scratch/release/check_stage.py`. Đây là **kiểm nội dung**, không phải
kiểm mã thoát: mỗi chặng bị hỏi 'kết quả có hợp lý không', không phải 'có chạy không'.

| Chặng | Kết luận | Chi tiết |
|---|---|---|
| ✅ verify | ĐẠT | giữ 3/3, đòi lại 3/3 — lượt-4-cộng-thêm an toàn | môi trường sạch, build 722868b, 1 luồng |
| ✅ marathon | ĐẠT | 99/99 = 100.0% (kỳ vọng ≥95% — Solo cùng đề đạt ~99%) | môi trường sạch, build e757688, 1 luồng |
| ✅ sweep | ĐẠT | 2464/2469 (nền 2434, chênh +30) | môi trường sạch, build 9e65773, 1 luồng |
| ✅ audit | ĐẠT | 2464/2469 — mọi dòng có dấu thuộc build đem nộp (165 chấm lại, 2113 đối chứng GIỐNG, 191 delta) |
| ◐ sieve | DỞ DANG | 200/608, frontier=50 |
| ⚠️ harvest | NGỜ | 22,307 dòng | dương 1,636 âm 20,671 (tỉ lệ 7.3%) | ⚠️ ĐO TRONG TRANH CHẤP: tải đỉnh 10.99/8.5, đối thủ 0 — số này KHÔNG dùng được |
| ⚠️ census | NGỜ | 1 họ route, lớn nhất: tổng | ⚠️ ĐO TRONG TRANH CHẤP: tải đỉnh 15.46/8.5, đối thủ 0 — số này KHÔNG dùng được |
| · label | CHƯA CHẠY |  |

Không có chặng nào HỎNG.
