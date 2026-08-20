# Khởi động lại sau khi máy ngủ / tắt / mất điện

## TỰ ĐỘNG — không cần nhớ gì

Đã cài dịch vụ hệ thống `com.magmaballz.chain`:

- chạy **khi đăng nhập** (sống qua khởi động lại máy)
- gọi lại **mỗi 10 phút** (nên tự tiếp tục sau khi máy ngủ dậy)
- có **khóa nguyên tử**: gọi chồng thì thoát ngay, không bao giờ chạy hai lượt
- khóa mồ côi sau mất điện được tự dọn ở lần gọi kế tiếp
- chạy ở mức ưu tiên thấp (`Nice 10`, `LowPriorityIO`) nên không giành máy với bạn

Kiểm tra:

```bash
launchctl list | grep magmaballz          # đang được quản lý chưa
bash .scratch/release/run_chain.sh status # chặng nào xong, chặng nào chưa
tail -f .scratch/release/../../../private/tmp/.../chain.log   # hoặc xem chain.log
```

Gỡ khi xong việc:

```bash
launchctl unload ~/Library/LaunchAgents/com.magmaballz.chain.plist
```

## Thủ công (nếu cần)

Một lệnh duy nhất, chạy lại bao nhiêu lần cũng được:

```bash
bash /Users/nhatminh/dev/active/MagmaBallz/.scratch/release/run_chain.sh
```

Nó tự bỏ qua các chặng đã xong và tiếp tục từ chặng dở. Xem trạng thái mà
không chạy gì:

```bash
bash .scratch/release/run_chain.sh status
```

Chạy nền để đóng terminal vẫn tiếp tục:

```bash
nohup bash .scratch/release/run_chain.sh > /dev/null 2>&1 &
```

## Vì sao an toàn

| Chặng | Dấu hoàn thành | Resume bên trong |
|---|---|---|
| verify_additive | `VERIFY ADDITIVE DONE` trong log | không cần (6 bài) |
| Marathon | log có dòng điểm | chạy lại từ đầu (~30 phút) |
| sweep chứng nhận | `final_cert.jsonl` đủ 2469 dòng | chạy lại từ đầu (vài giờ) |
| sieve Forge | `DONE:` trong log | **có sổ cái** `checked_v1.jsonl` |
| harvest ML | `HARVEST DONE` | **có sổ cái** `harvested_ids.txt` |
| census route | `ROUTE CENSUS DONE` | chạy lại từ đầu |
| label_doubt | `LABEL DOUBT DONE` | có danh sách bỏ qua cấu hình đã trượt |

Hai chặng dài nhất (sieve, harvest) đều ghi sổ cái sau mỗi đơn vị việc, nên
mất điện tốn tối đa **một đơn vị**, không phải cả chặng.

## Gói nộp

```bash
bash .scratch/release/make_submission.sh          # từ HEAD
bash .scratch/release/make_submission.sh <commit> # từ commit cụ thể
```
Xuất ra `.scratch/release/submission/` gồm `solver.py`, `SUBMISSION_NOTE.md`,
`BUILD_COMMIT.txt`, và **từ chối xuất nếu vi phạm bất kỳ ràng buộc nộp bài nào**.

## Mốc thời gian

- Đóng băng + nộp bản bảo hiểm: **26/08 12:00 giờ VN** (trước khi ra sân bay đêm 26/08)
- Quãng nghỉ khi bay: 26/08 đêm → 27/08 tối giờ Mỹ (máy có thể tắt — dùng lệnh trên để chạy tiếp)
- Cửa sổ làm việc lần hai: 27/08 tối giờ Mỹ → **hạn 01/09 07:59 EDT / 04:59 PDT**
