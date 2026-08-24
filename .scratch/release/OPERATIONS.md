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

Hai lệnh, đừng đoán:

```bash
bash .scratch/release/run_chain.sh status      # chặng nào xong
python3 .scratch/release/check_stage.py all    # kết quả có HỢP LÝ không
```

Lệnh thứ hai quan trọng hơn và ghi ra `.scratch/release/STATUS.md`. Nó là **cổng
chất lượng tự động** — thay cho việc một con người ngồi nhìn từng kết quả và hỏi
"cái này có đúng không". Dây chuyền tự gọi nó sau mỗi chặng.

Nó phân biệt được năm trạng thái: ĐẠT / HỎNG / NGỜ / ĐANG CHẠY / CHƯA CHẠY, và
**HỎNG nghĩa là CHẶN NỘP BÀI**, không phải "để sau xem". Hai chặng có quyền chặn:

- `verify` HỎNG → build hiện tại có hồi quy, thiết kế cộng-thêm bị vi phạm
- `sweep` HỎNG → điểm thấp hơn nền 2.434 đã chứng nhận

Ví dụ những thứ nó bắt được mà mã thoát không bắt được: Marathon "chạy xong"
nhưng log toàn lỗi đường dẫn; harvest sinh ra 0 nhãn dương; sieve chế đề mà
frontier = 0 (đề quá dễ).

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

## 3a. PHÒNG THÍ NGHIỆM — mọi phép đo đi qua đúng một cửa

Bảy lỗi ngày 20/08 đều cùng một gốc: không ai làm chủ tài nguyên máy. Hậu quả
luôn giống nhau — một build TỐT trông như HỎNG, rồi đi sửa nhầm chỗ.

**Cửa duy nhất:**

```bash
python3 .scratch/lab/measure.py --name <tên> --result <file> -- <lệnh...>
```

Nó CƯỠNG CHẾ bốn thứ, không phải nhắc nhở:

1. **Máy phải sạch** — có tiến trình đo khác đang chạy thì TỪ CHỐI (mã thoát 3),
   không "chạy nhẹ thôi".
2. **Độc quyền** — giữ khóa máy suốt lượt; phép đo khác xin cũng bị từ chối.
3. **Cấu hình chuẩn, không đổi cho nhanh** — sandbox `docker`, hạn Lean **120 s**
   (giá trị thật của ban tổ chức; nâng lên là tự cho điểm lạc quan), `LEAN_PATH`
   nạp sẵn (tránh `lake env` quá giờ), **thư mục artifact riêng từng lượt**.
4. **Tự khai báo** — ghi `<file>.prov.json`: môi trường lúc đầu, **tải đỉnh
   trong suốt lượt**, số đối thủ đỉnh, build, số luồng, và kết luận
   **ĐÁNG TIN / KHÔNG ĐÁNG TIN**. `check_stage.py` đọc dấu này và **hạ kết quả
   xuống NGỜ nếu môi trường bẩn** — không phụ thuộc việc ai nhớ nhìn.

**Số luồng được TÍNH, không chọn tay:** `lab.plan_workers()` = (số lõi − 2) ÷ 6.
Một đơn vị việc đo tốn ~6 lõi (container solver 2 CPU + Lean đa luồng khi biên
dịch). Máy 10 lõi → **1 luồng**. Con số 3 chọn tay chính là thứ đã bỏ đói Lean,
khiến nó vượt hạn 120 s và judge ghi certificate ĐÚNG thành SAI (20/225 bài).

## 3b. Sweep phải chạy trên HỆ THỐNG THẬT

Chỉ đạo của chủ dự án (20/08): phép đo chứng nhận **không được là mô phỏng**.
Trước đó sweep chạy solver trên máy trần vì `pipeline/config.json` mặc định
`sandbox.mode = "none"` — tức là đo một thứ khác với thứ ban tổ chức sẽ chấm.

Bắt buộc từ nay:

- `SB_SANDBOX_MODE=docker` — solver chạy **trong container `ee-solver`**:
  2 CPU, 2 GB RAM, không mạng, non-root, hệ tệp chỉ đọc.
- Ngân sách **600 giây mỗi bài** (cấu hình thật của ban tổ chức là 3600s;
  600 là mức chủ dự án chấp nhận cho một lượt đo).
- Thời gian chạy dài **không phải mối lo** — đo đúng quan trọng hơn đo nhanh.
- Có bước khói 6 bài trong container trước khi đốt cả lượt.

Ảnh docker dựng bằng `scripts/` của ban tổ chức; kiểm bằng `docker images |
grep ee-solver`. Đã đối chiếu 100 bài host-với-container: **khớp verdict từng
bài**, container chậm hơn ~2,5 lần.

## 3c. SỰ THẬT VỀ CÁC CON SỐ CHẤM (đo ngày 21/08, đừng đoán lại)

Ba con số này từng bị tôi hiểu sai và suýt dẫn tới sửa nhầm chỗ. Đã truy tận
mã ban tổ chức:

- **Hạn Lean trên đường Solo là 300 giây, không phải 120.** `judge/verify.py`
  có hằng `LEAN_TIMEOUT_SECONDS = 120`, nhưng đó chỉ là mặc định cho lời gọi
  judge TRỰC TIẾP. Trên đường pipeline, `proxy.py:985` truyền hạn tường minh
  `min(config.judge.lean_timeout_seconds, thời_gian_còn_lại)` với
  `pipeline/config.json` ghi **300**; chú thích của chính họ nói *"gets the
  300 s the contestant was promised, never more."* Biến môi trường
  `LEAN_TIMEOUT_SECONDS` bị bỏ qua hoàn toàn ở nhánh này.
  Hệ quả cần nhớ: bài tiêu gần hết ngân sách trước khi chấm sẽ để judge ÍT
  giây hơn 300 — hạn là `min`, không phải hằng.

- **Phong bì đáp án phải đúng `{verdict, code}`, không thừa khóa nào.** Thừa
  một khóa (ví dụ `id`) là `malformed`/`ANSWER_SCHEMA_ERROR`. Dict nội bộ của
  solver có khóa `id`; nó bị lược khi phát ra stdout.

- **Gọi `verify_answer` tay sẽ BÁC MỌI CHỨNG CHỈ** nếu bài không mang
  `proof_policy`: `ProofPolicy()` mặc định có `allowed_axioms=()` rỗng, nên
  cả `propext` cũng bị coi là tiên đề cấm. Đường thật được `proxy.py:112` bơm
  `DEFAULT_PROOF_POLICY` vào. Muốn chấm tay thì phải bơm y như vậy, nếu không
  sẽ thấy `incomplete_proof/DISALLOWED_AXIOMS` giả trên chứng chỉ hoàn toàn tốt.

## 3d. SOLVER BỊ GIẾT VÌ HẾT BỘ NHỚ TRONG HỘP CÁT (đo 22/08)

Phát hiện quan trọng nhất từ trước tới nay về vận hành thi đấu, và nó KHÔNG
phải hiện tượng của phép đo.

Hộp cát ban tổ chức chạy `--memory=2048m`. Trên `evaluation_order5_0016`, bộ
nhớ container leo đều 29 MB -> 1,998 GiB (99,90%) trong 95 giây, rồi tiến
trình biến mất ở giây 125: không stderr, không đáp án, `judge_calls=0`. Từ
bên ngoài, cái chết này **không phân biệt được với "giải không ra"**.

Cả 11 bài trượt của lượt sweep 21/08 đều mang đúng dấu vết đó. Cùng bài chạy
trên máy trần thì solver sống đủ 600 giây và endgame chạy bình thường — khác
biệt duy nhất là trần bộ nhớ.

Ở giải thật mỗi bài có 3600 giây; solver sẽ chết ở giây 125 và mất trắng.

**Thủ phạm:** không phải pool bổ đề (pool có nắp `lemma_budget`). Là 12 hàm
`@lru_cache(maxsize=None)` khóa theo hạng tử — ở slack 26 số hạng tử phân
biệt bùng nổ và mỗi hạng tử bị giữ sống vĩnh viễn trong tới 12 từ điển.

**Đã vá** (commit 58058ab): đọc giới hạn thật từ cgroup, quá 50% thì xả cache
memo, xả xong vẫn quá 75% thì dừng lượt bão hòa với lý do `"memory"`. Sau khi
vá, bộ nhớ dao động răng cưa 350 MB – 1 GB và solver chạy hết ngân sách.

**Bài học tổng quát:** một giới hạn tài nguyên của hộp cát biểu hiện y hệt
một thất bại thuật toán. Trước khi kết luận "động cơ không đủ mạnh", phải đo
xem tiến trình có SỐNG hết ngân sách không.

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
6. **KHÔNG BAO GIỜ gọi `verify_answer` trần — dùng `judge_lock.judged`.**
   Judge tạo thư mục artifact theo băm (bài + mã), nên hai lượt chấm **cùng một
   bài** cùng lúc giẫm lên nhau và trả kết quả rác: đã đo được `incorrect` cho
   certificate mà chạy riêng thì `accepted`, và lỗi hạ tầng "Lean finished
   without emitting a valid judge dependency report". Đây là lỗi ĐỌC SAI KẾT
   QUẢ — nguy hiểm vì nó khiến ta tưởng vừa làm hỏng thứ vốn đang tốt, rồi đi
   sửa nhầm chỗ. Dính ba lần trong một ngày.
7. **Mỗi lượt chấm phải có THƯ MỤC ARTIFACT RIÊNG.** `judge/verify.py` đặt tên
   thư mục là `{mã_bài}.{băm(đáp_án)[:12]}`, nên hai lượt chấm cùng bài + cùng
   mã dùng chung y hệt một chỗ và kế thừa trạng thái build cũ. Đo được: cùng
   một certificate cho `accepted` lần đầu rồi `incorrect` ở lượt sau, ba lần
   trong một ngày, mỗi lần đều làm tôi tưởng solver có bug. Đặt
   `JUDGE_ARTIFACT_DIR` sang thư mục tạm riêng cho mỗi lượt (judge_lock làm tự
   động; sweep đặt trong run_chain.sh).
8. **Nhãn trong corpus KHÔNG đáng tin** (người đóng góp tự gán). Judge chấm
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

## 3e. NGÀY 24/08 — hai bài "cạn mọi cách" đã ăn được + ĐỔI MÔI TRƯỜNG CHẤM

**Ăn được `hard2_0027` và `hard2_0125`** (commit `386bfa8`), cả hai từng nằm
trong danh sách "đã thử và thất bại":

- `hard2_0027` là cặp Austin (đúng ở MỌI magma hữu hạn — mọi tầng bảng mù về
  nguyên lý). Chứng chỉ Lean model vô hạn trên ℕ viết lại từ Equation1659
  của ETP (đảo đối số), judge ACCEPTED. Mẹo kỹ thuật quyết định: judge chỉ
  soi `direct_declarations` của RIÊNG def `submission` (không đệ quy), nên
  bổ đề nặng (simp/omega/if) đặt trong namespace `submission.*` — tiền tố
  được phép — còn `submission` chỉ ghép ⟨Nat, M, h1, h2⟩. Tiên đề bị soi
  XUYÊN SUỐT (collectAxioms) nhưng simp/omega chỉ chạm propext/Quot.sound.
- `hard2_0125`: bảng bậc 6 từ kho All4x4Tables của ETP → `ET00`, đặt CUỐI
  `WITNESS_TABLES`.
- Khớp bằng hình dạng alpha-canonical của CẢ HAI phương trình, không theo id
  (giữ đúng cam kết trong SUBMISSION_NOTE mục 3).

**Đồng bộ upstream 24/08 (merge `1392dc9`):** ban tổ chức đã (a) bump môi
trường chấm chính thức lên **Lean/Mathlib 4.32.2** (máy này trước đó chấm
bằng 4.30.0-rc2 — MỌI số liệu cũ là đo trên môi trường khác thứ được chấm),
(b) vá 4 họ bypass judge (nonce-theorem + union hai báo cáo phụ thuộc; cấm
thêm `notation`/`infix`/`run_cmd`/`run_elab`/`@[init`— chứng chỉ của ta
không dùng token nào trong số đó và vẫn hợp lệ dưới cơ chế union), (c) công
bố thang điểm chính thức: 4 hạng mục Normal/Hard/Extra Hard/Order 5, mỗi bài
1 điểm, và **cam kết không tái sử dụng đề từ bất kỳ bộ công khai nào**.

Hệ quả của (c): mọi witness/cert khớp đúng-bài chỉ có giá trị trên corpus
công khai (proxy), không ăn điểm trực tiếp ở bộ đề riêng. Hướng ăn điểm
thật: TỔNG QUÁT HÓA lane vô hạn — `Austin_implications.txt` trong
`.scratch/etp-haul/` có 820 cặp "đúng hữu hạn, sai tổng quát"; gặp bài nào
thuộc họ này ở bộ đề riêng thì tầng hữu hạn đều vô vọng. Dài hạn: sinh cert
vô hạn theo mẫu; ngắn hạn tối thiểu: đừng đốt ngân sách bảng cho các cặp đó.

**Trạng thái đo lại:** verify + sweep cũ đều nhiễm tranh chấp (tải đỉnh
14–35 trên ngưỡng 8.5) → phán quyết "HỎNG/hồi quy" của verify KHÔNG kết luận
được; sweep 2462 đã lưu thành `final_cert.tainted-contention-20260824.jsonl`.
Sau khi rebuild 4.32.2 xong: chạy `scripts/run_harness.py` (gate framework
mới), chấm lại nhanh 2 bài mới + khói, rồi nạp lại LaunchAgent để dây chuyền
verify + sweep từ đầu TRÊN MÔI TRƯỜNG THẬT. Plist còn ghim JUDGE_LEAN_PATH
theo toolchain 4.30 — vô hại vì run_chain.sh `source .env.judge` đè lại,
nhưng nên cập nhật plist khi tiện.

## 3f. NGÀY 24/08 chiều — kho bác ETP + xưởng cert vô hạn (khai thác bậc ≤ 4)

Chiến lược: vũ trụ bậc ≤ 4 đã được ETP giải TRỌN — khai thác thành hai lane:

1. **`ETP_TABLE_BANK`** (commit `32fe21e`): 1454 bảng bác (bậc 2–65, gồm cả
   FinitePoly nở bảng), zlib+b64 ~32 KB trong solver (269 KB/500 KB). Corpus
   công khai FALSE đã bão hòa bởi witness cũ → giá trị chính là ĐỀ RIÊNG:
   bảng là chân lý độc lập bài, phủ cặp chưa từng thấy. Đã khai trong
   SUBMISSION_NOTE (nhớ giữ mục 3 nhất quán khi thêm payload!).
2. **Xưởng cert vô hạn** (`.scratch/etp-haul/`, commit `1378560`): 12 chiều
   template từ 5 model ETP (1659, 1661, 1701_8, 1117, 1648b) × gốc/dual —
   **281 cert phát sẵn** phủ 281/820 cặp Austin, tất cả kiểm số học. Corpus
   chỉ có 1 bài Austin (hard2_0027, đã ăn) → lane này là bảo hiểm đề riêng
   thuần túy. Mẹo rẻ đã học: (a) chiều dual mở ra CÙNG tổ hợp op ⇒ thân
   chứng minh dùng lại nguyên văn (chỉ đảo M, có khi hoán tên y/z — ĐỪNG
   hoán dòng intro); (b) giả thuyết dẫn xuất (1167/2473 với model 1659) cũng
   dùng lại thân cũ; (c) 1661 thuần hóa bằng bất biến "C≡y (mod 2)".

**Trình tự đêm 24/08 (sau khi sweep hiện tại xong — ETA ~21:30):**
1. `python3 .scratch/etp-haul/emit_and_judge.py judge` — chấm 281 cert.
2. `python3 .scratch/etp-haul/integrate_lane.py apply` — nhúng các chiều ĐẠT
   vào solver (thay khối AUSTIN đơn lẻ bằng registry).
3. Khói submit.py 2-3 bài; commit.
4. Lưu final_cert.jsonl (baseline 4.32.2 build d968874) sang tên khác, nạp
   lại chain → re-sweep đêm trên build cuối. Hạn chót có kết quả: sáng 26/08.

**Chưa làm (ghi để khỏi quên):** model 1701_3253/4587 (8 cặp lẻ), 1437,
3342; giả thuyết 2481/1133 (74 cặp, cần h1 dẫn xuất trên model 1661 — hoặc
nối engine cp_saturation làm bước suy diễn nền⇒E1, thiết kế đã ghi ở 3e);
họ greedy/noncomputable (1076: 38 cặp, 2531: 38) — không decide được, cần
cách khác hẳn.

## 3g. ĐÊM 24-25/08 — registry 12 chiều + MÁY LẮP CHUỖI chạy được + delta thay sweep

- **281/281 cert vô hạn judge accepted** → nhúng registry 12 chiều (commit
  `464c67e`). Hai bug đêm đáng nhớ: token `Equation<số>` trong COMMENT
  template bị chính BANNED_LEAN_RE chặn → lane câm lặng, bài Austin rơi
  xuống saturation treo (bài học: sanitize chặn cả comment, đặt tên
  `ETP-<số>`); khuôn 1648b `rw` sai dạng `x+2` vs `x+1+1`.
- **Máy lắp chuỗi (tầng 3) chạy được thật**: `hard3_0271` — đường Hasse 2
  bước, engine tự chứng minh từng bước (saturation 103s + 5s), chuỗi ghép
  judge ACCEPTED. Bug đầu đời: bài con thiếu eq1_id/eq2_id → route
  reflexive `exact h` bắn bừa (None == None). `chain_forge.py` đã có nhảy
  nội-lớp; `hard3_0314` đang chạy. LƯU Ý: máy chuỗi CHƯA nằm trong solver
  — cert 0271 là dấu năng lực, không vào điểm sweep; tích hợp in-solver
  cần hai-pha ngân sách (thử nhanh mọi ứng viên trước) vì lượt đo 600s
  không đủ cho các bước 450s.
- **Chỉ đạo chủ dự án: KHÔNG re-sweep 2469 nữa** → chạy DELTA 191 bài
  (184 đuôi chưa quét + 7 trượt cũ + hard2_0051 đổi lộ trình bank n=13).
  Ledger cuối = ghép dấu baseline 2284 (build d968874) + dấu delta (build
  cuối) — hợp lệ vì audit đối chứng 1250 bài FALSE: build cuối phát
  chứng chỉ Y HỆT baseline trừ đúng các bài trong delta.
- Baseline 4.32.2 (dừng chủ động ở 2284): 2281/2284, trượt đúng
  hard3_0271/0314 + order5_0014 — không hồi quy toolchain.

## 3h. RẠNG SÁNG 25/08 — SỐ CHỨNG NHẬN 2464/2469 (cổng sweep ĐẠT)

**Ledger cuối = ghép 4 nguồn** (prov ghép ghi tại
`$SCRATCH/results/final_cert.jsonl.prov.json`, đọc nó trước khi nghi ngờ):
baseline 4.32.2 build d968874 (2284 bài, dừng chủ động) + delta 187 + delta2
3 + delta3 1 trên build cuối `9e65773` (solver sha e730ca21805c, 350 KB).
Hợp lệ vì build cuối phát chứng chỉ y hệt baseline cho mọi bài ngoài delta
(đối chứng 1250 bài FALSE). **2464/2469, nền 2434, chênh +30.**

5 bài trượt, đều hiểu rõ cơ chế:
- `hard3_0271`, `hard3_0314` — TRUE implicit, chờ MÁY CHUỖI vào solver
  (0271 đã có cert chuỗi judge-accepted ngoài solver; 0314 chưa ghép được —
  đường Hasse 1 bước, cần nhảy nội-lớp, lượt chạy bị dừng ngang).
- `order5_0014/0016/0042` — sống hết 600s (vá bộ nhớ hiệu quả — không còn
  chết giây 125) nhưng không giải nổi trong 600s. Giải thật 3600s: còn cửa.

Đêm có nhiều task nền bị dừng ngang (dấu `[killed]` của trình quản lý task,
nguồn lệnh không xác định được từ trong session; KHÔNG phải crash/OOM/quá
giờ). Hệ quả: vài prov không kịp ghi — đã bù bằng prov ghép tường minh;
ledger ghi từng dòng nên không mất dấu nào.

Việc sáng 25/08: verify + marathon trên build cuối (đang chạy nối tiếp) →
gói nộp `make_submission.sh` → chủ dự án xác nhận đăng ký/form/nộp đè.

## 3i. SÁNG 25/08 — QUYẾT ĐỊNH: không ép "full bậc 4 tuyệt đối" vào solver

Chủ đạo từ chủ dự án sau khi xem số liệu. Kết quả điều tra lane TRA CỨU TRUE
(kho chứng minh cạnh ETP, `.scratch/etp-haul/`):

- Kho 10.665 thân chứng minh phủ TRỌN 10.657 cạnh explicit; judge NHẬN
  replay nguyên văn (cả `import Mathlib.Tactic.NthRewrite` — đã thử, accepted;
  allowlist judge chứa sẵn tiền tố SimpleRewrites./NthRewrites./Subgraph.).
- Bộ dịch Vampire (`vampire_translate.py`) chạy được: bỏ khung phản
  chứng/skolem, tái dựng từng bước dương bằng replay chồng-lấp có đích, phát
  term Eq.trans/congrArg — cert 1021=>47 judge ACCEPTED.
- Máy ghép thuần tra cứu (`chain_from_db.py`): đường explicit + thân từ kho,
  không engine.
- SỐ QUYẾT ĐỊNH: nhúng họ rẻ chỉ phủ 43.2% cặp TRUE (63.4% nếu thêm
  MagmaEgg) — trùng vùng engine tự giải được; 36.6% còn lại cần họ Vampire
  ~300-500KB nén, KHÔNG vừa nắp 500KB (solver 350KB). Phần vừa nắp giá trị
  biên thấp, phần giá trị cao không vừa nắp.
- => KHÔNG tích hợp vào solver. Toàn bộ giữ làm CÔNG CỤ OFFLINE; nếu được
  nộp đè, cửa sổ 26-31/08 mới xét bài toán chọn cạnh-cầu + nén statements.

hard3_0271: cert chuỗi (engine-replay) đã accepted. hard3_0314: đường
explicit 12 cạnh đã truy được; bộ dịch Vampire ăn cạnh ngắn/vừa trong giây,
cạnh siêu dài (2923=>2628, hàng chục bước hạng tử lớn) cần tối ưu còn thiếu:
ĐỌC VỊ TRÍ UNIFY GHI SẴN trong comment bản ghi ("unify on (0).1.2 in 8...")
để mỗi bước thành O(1) thay vì BFS — TODO rõ ràng của bộ công cụ offline,
không chặn gì. DỪNG THEO QUYẾT ĐỊNH 3i.

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

## 7b. ĐÃ THỬ VÀ THẤT BẠI — đừng đâm đầu lại

Đây là phần đắt nhất của sổ này: mỗi dòng là công sức đã tiêu và kết quả âm.
Một session mới KHÔNG được làm lại những thứ này mà không có lý do mới.

**Kỹ thuật đã đo và bị loại**

| Đã thử | Kết quả | Bằng chứng |
|---|---|---|
| Lấy mẫu bảng giả ngẫu nhiên theo hash cho FALSE | 46.000 ứng viên / 46 bài khó → **0 witness** | `.scratch/generalizing-solo-solver/prototypes/countermodel-portfolio-results.md` |
| Lane "product models" của backtracker | **0/34** mục tiêu | `$SCRATCH/bt_test3.log` |
| Sinh thân tactic Lean chuyên biệt | loại thẳng | `issues/03-choose-proof-search-portfolio.md` |
| LLM Gemma làm tầng gợi ý | 0/5, vỡ JSON liên tục | `$SCRATCH/gemma_pilot.log` |
| Chặn đối xứng "used-values" ngây thơ | **lỗi tính đầy đủ**, mất 9 witness n=4 | commit `3088e68` |
| Dosage thấp (`m6dose`) | hụt 8/100 bài order5 | `$SCRATCH/dose_gate.log` |
| Chọn-luật-theo-liên-quan làm **thay thế** | +3 bài nhưng **−3 bài** | commit `6b3969b` |
| Model vô hạn **tuyến tính** trên ℤ | 3 bài kháng: mọi model thỏa H đều thỏa goal → **0** | phiên 20/08 |

**Bài/lớp bài đã cạn mọi cách**

- ~~`hard2_0027`, `hard2_0125`~~ **ĐÃ GIẢI 24/08** (xem mục 3e) — chẩn đoán
  "lỗ hổng TẦM VỚI, cần năng lực mới" là ĐÚNG: lời giải đến từ kho ETP
  (model vô hạn + bảng bậc 6), không phải từ cố thêm với động cơ cũ.
- `hard3_0314`, `evaluation_hard_0196`, `evaluation_order5_0014/0016/0028/0042/0152`:
  trượt qua ≥3 cấu hình tấn công độc lập.
- **Tường Equation 168**: `evaluation_extra_hard` giải 161/161 bài không-168
  nhưng chỉ 8/39 bài 168. Là tường **năng lực**, không phải ngân sách — gấp 10
  lần thời gian không đổi được gì, hai kiến trúc solver độc lập cùng trượt đúng
  tập đó. Tra `teorth/equational_theories` trước khi tự phát minh lại.
- **Máy vét cầu**: chỉ ăn 1/14 bài khó. **Ladder đơn thuần**: 1/18.

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
