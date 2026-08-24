# BÁO CÁO TOÀN CẢNH — solver EQT02-M00006 và mọi phép đo (tính đến sáng 25/08/2026)

Tài liệu này giải thích **cơ chế đầy đủ của solver** và **lịch sử mọi phép đo**
từ đầu chiến dịch đến hiện tại. Tham chiếu kỹ thuật từng hàm nằm ở
`SOLVER_DOCS.md`; công bố dữ liệu nộp kèm nằm ở `SUBMISSION_NOTE.md`; nhật ký
vận hành nằm ở `.scratch/release/OPERATIONS.md`.

---

## Phần I — Bài toán và luật chơi

Mỗi bài cho hai phương trình trên magma (một tập với đúng một phép toán `◇`,
không tiên đề nào khác): **E1 có kéo theo E2 trong MỌI magma không?** Solver
không được trả lời suông — phải nộp **chứng chỉ Lean 4**:

- **TRUE**: chứng minh `∀ (G) [Magma G], E1(G) → E2(G)`.
- **FALSE**: chứng minh `∃ (G) (_ : Magma G), E1(G) ∧ ¬E2(G)` — carrier được
  phép hữu hạn (bảng `Fin n`) **hoặc vô hạn** (`Nat`, `Int`, inductive tự
  định nghĩa).

Judge là trình biên dịch Lean tất định, trả đúng 1 trong 5 trạng thái
(`accepted` / `unparsed` / `malformed` / `incomplete_proof` / `incorrect`),
kèm hai hàng rào: **tiên đề** chỉ được `propext`, `Quot.sound`,
`Classical.choice` (soi xuyên suốt qua `collectAxioms`), và **khai báo trực
tiếp** của `submission` phải khớp danh sách tiền tố cho phép (soi *không*
đệ quy — chi tiết này quan trọng, xem Phần III).

Môi trường chấm thật: solver trong sandbox **2 CPU / 2 GB RAM / không mạng /
hệ tệp chỉ đọc**; mỗi bài Solo 3600 s; Lean của judge được hứa 300 s;
verification stack **Lean/Mathlib 4.32.2**. Điểm: 4 hạng mục
(Normal/Hard/Extra Hard/Order 5), mỗi bài accepted = 1 điểm. Đề chấm là bộ
riêng, **cam kết không tái dùng** từ bất kỳ bộ công khai nào. Nộp: một file
`solver.py` ≤ 500 KB, chỉ thư viện chuẩn (+sympy), kèm ghi chú công bố dữ
liệu. Hai chế độ thực thi: **Solo** (một tiến trình/bài, JSON qua
stdin/stdout, LLM đi qua proxy của ban tổ chức) và **Marathon** (một tiến
trình cho N bài, ngân sách chung, phải triage).

---

## Phần II — Cơ chế solver: thứ tự xử lý một bài

Solver là **thác các tầng tất định**, rẻ trước đắt sau; tầng nào phát được
chứng chỉ thì dừng. Mọi thứ phát ra đều tự kiểm cục bộ trước
(`table_is_counterexample` cho bảng, `sanitize_lean_code` cho Lean), và
judge luôn là người phán cuối — solver không tin dữ liệu nhúng một cách mù.

**Bước 0 — Oracle ETP (chỉ chia ngân sách).** Tra bao đóng kéo theo của toàn
vũ trụ 4694 phương trình bậc ≤ 4. Nếu cặp nằm trong vũ trụ: biết trước
TRUE/FALSE. Dùng đúng một chỗ: bài chắc TRUE thì ngân sách tìm phản mẫu bị
bóp còn 2 s (đủ quét hai kho bảng) thay vì đốt nhiều phút. Không bao giờ
phát, chặn, hay đổi thứ tự chứng chỉ — nên không thể làm sai điểm.

**Tầng 1 — TRUE mẫu nhanh** (mili-giây): reflexive → singleton (E1 ép magma
1 phần tử) → họ collapse (middle/front/alternating self-collapse) →
sandwich/projection → thế trực tiếp một bước → bridge → absorption
context/closure.

**Tầng 2 — FALSE hữu hạn** (`find_counterexample`, leo thang):
1. 232 bảng witness có tên (`LP`/`XOR`/…/`CG9`/`MW`/`HV`/`ET00`);
2. **kho bác ETP 1454 bảng** (bậc 2–65, bậc nhỏ quét trước);
3. họ bảng cấu trúc (semilattice, spine, conditional, rectangle band);
4. họ affine `(ax+by+c) mod n` rồi bậc hai;
5. vét cạn mọi bảng n ≤ 3;
6. lặp lại toàn bộ với bài đối ngẫu.

Tìm ra bảng → cert `finOpTable` (n ≤ 10) hoặc List-literal với số học
bare-function (n ≥ 11 — né bug giải mã từng-chữ-số của `finOpTable` và lệnh
cấm toán tử typeclass).

**Tầng 3 — lane model VÔ HẠN** (chỉ khi tầng 2 trắng tay hoàn toàn — nguyên
tắc cộng-thêm): khớp *giả thuyết* với registry 12 chiều model ETP theo hình
dạng alpha-canonical; tìm điểm vi phạm E2 bằng quét cửa sổ tất định; phát
chứng chỉ Lean model vô hạn với điểm vi phạm điền động. Đây là cửa duy nhất
cho các **cặp Austin** — đúng ở mọi magma hữu hạn, chỉ sai trên carrier vô
hạn, nên mọi tầng bảng mù về nguyên lý.

**Tầng 4 — TRUE nặng**: equational closure / deep absorption (BFS hai chiều
trên không gian term) → **cp_saturation** (động cơ chính: sinh bổ đề
critical-pair có nắp ngân sách, kèm chốt bộ nhớ: quá 50 % trần cgroup thì xả
cache memo, vẫn quá 75 % thì dừng lượt với lý do `"memory"`) → standard
ladder (8 đích trung gian cổ điển) → bridge enumeration.

**Tầng 5 — vét cuối**: LLM qua proxy (Solo; solver không bao giờ giữ API
key) hoặc bỏ qua theo triage (Marathon), rồi endgame passes lặp tới hết giờ.

### Các kho tri thức nhúng (tự chứa trong file, tổng ~350 KB / nắp 500 KB)

| Kho | Cỡ | Nội dung | Vai trò |
|---|---|---|---|
| `WITNESS_TABLES` | ~21 KB | 232 bảng có tên: 26 magma cổ điển, CG9 (central groupoid phi tự nhiên bậc 9), 200 bảng harvest từ artifact judge (đã kiểm lại từng bảng) | Tầng FALSE đầu, giữ nguyên witness cho bài cũ |
| `ETP_TABLE_BANK_B64` | ~32 KB nén | 1454 bảng bác từ All4x4Tables + FinitePoly của ETP, dedup, bậc 2–65 | Tập bác (gần) đầy đủ cho vũ trụ bậc ≤ 4 — phủ cả đề chưa từng thấy |
| `ETP_ORACLE_B64` | ~26 KB nén | Bao đóng kéo theo 4694×4694 rút không mất mát về 1415 lớp tương đương + 4824 cạnh Hasse; 190 cặp ngoại lệ (conjecture/unknown tại snapshot 2024-11-10) oracle nhịn | Biết trước đáp án mọi cặp bậc ≤ 4; chỉ chia ngân sách |
| `ETP_EQUATIONS_B64` | ~15 KB nén | 4694 phương trình ETP nguyên văn | Ánh xạ đề → mã ETP bằng hình dạng alpha-canonical (không theo id bài) |
| `INFINITE_MODEL_LANE` | ~30 KB | 12 chiều × 5 model vô hạn ETP (1659 ×4 hướng, 1661 ×2, 1701a ×2, 1117 ×2, 1648b ×2), mỗi chiều một template Lean đã được judge phê + op mô phỏng Python | Tầng 3; phủ 281/820 cặp Austin |

Mẹo kỹ thuật then chốt của các template vô hạn: judge chỉ soi
`direct_declarations` của **riêng** def `submission` (không đệ quy), nên mọi
bổ đề nặng (simp/omega/if) đặt trong namespace `submission.*` — tiền tố được
phép — còn `submission` chỉ ghép `⟨Carrier, M, h1, h2⟩`. Tiên đề vẫn bị soi
xuyên suốt nhưng simp/omega không vượt quá `propext`/`Quot.sound`.

### Máy lắp chuỗi (đang là prototype ngoài solver)

Với bài TRUE mà cú nhảy tổng thua: tìm đường trên đồ thị Hasse
`C(E1) → … → C(E2)`, mỗi bước nhờ chính engine chứng minh như một bài con
(kèm nhảy nội-lớp khi đường Hasse quá ngắn), rồi ghép
`have h1 := …; …; exact hk`. Đã ăn thật `hard3_0271` (judge accepted, chuỗi
2 bước). Chưa nằm trong solver — bản in-solver cần cơ chế ngân sách hai pha
(thử nhanh mọi ứng viên trước) vì một bước trượt có thể đốt 450 s.

### Nguyên tắc thiết kế (trả giá mới học được)

1. **Cộng-thêm, không thay thế**: mọi tầng mới đặt ở vị trí không thể cướp
   bài của tầng cũ; kiểm bằng phép đối chứng lộ trình chứ không bằng niềm tin.
2. **Không tin dữ liệu nhúng**: bảng nào cũng kiểm lại theo đúng bài trước
   khi phát; oracle không có quyền phát hay chặn.
3. **Không lookup theo problem id** — mọi khớp nối đi theo hình dạng phương
   trình (giữ đúng cam kết trong SUBMISSION_NOTE §3, và vì đề thật không tái
   dùng đề công khai nên khớp-theo-id là vô giá trị).
4. **Tất định tuyệt đối**: không ngẫu nhiên, không phụ thuộc giờ máy.

---

## Phần III — Lịch sử phép đo

### Hạ tầng đo (vì sao phải cầu kỳ)

Bảy lỗi ngày 20/08 có chung một gốc: *không ai làm chủ tài nguyên máy*, và
hậu quả luôn là **build TỐT trông như HỎNG rồi đi sửa nhầm chỗ**. Từ đó mọi
phép đo đi qua đúng một cửa `measure.py`: máy phải sạch (có phép đo khác →
từ chối), độc quyền suốt lượt, cấu hình chuẩn không đổi-cho-nhanh, và tự
khai môi trường vào dấu `.prov.json` — cổng chất lượng `check_stage.py` đọc
dấu này và **tự hạ kết quả xuống NGỜ nếu môi trường bẩn**. Các bài học đắt
đã đóng học phí:

- Tải máy làm lệch một sweep +4 rồi −18 bài → không đo và đánh cùng lúc.
- Hai lượt chấm cùng bài+mã dùng chung thư mục artifact → cùng một
  certificate lần đầu `accepted` lần sau `incorrect` (3 lần/ngày) → mỗi lượt
  chấm một artifact dir riêng, không bao giờ gọi `verify_answer` trần.
- Số luồng phải TÍNH từ số lõi (máy 10 lõi → 1 luồng); con số 3 chọn tay
  từng bỏ đói Lean khiến 20/225 certificate ĐÚNG bị chấm SAI.
- Chấm tay không bơm `proof_policy` → judge bác cả `propext` → thấy lỗi giả
  trên chứng chỉ hoàn toàn tốt.
- Sandbox 2 GB giết solver ở giây 125 mà bên ngoài **không phân biệt được
  với "giải không ra"** (OOM do 12 hàm `@lru_cache` không nắp) → vá chốt bộ
  nhớ; bài học: giới hạn tài nguyên biểu hiện y hệt thất bại thuật toán.
- Sweep phải chạy **trong container** (`ee-solver`: 2 CPU/2 GB/không mạng),
  600 s/bài — đo đúng thứ ban tổ chức chấm; đã đối chiếu 100 bài
  host-vs-container: khớp verdict từng bài.

### Dòng thời gian số liệu

| Mốc | Phép đo | Kết quả | Ý nghĩa |
|---|---|---|---|
| ≤ 20/08 | Sweep chứng nhận (máy sạch, không LLM, Lean 4.30) | **2434/2469** | Nền chứng nhận; +26 bài đòi lại có dấu judge riêng → trần lý thuyết 2460. Đối thủ mạnh nhất: 2411 |
| 21/08 | Sweep 2469 (build 9b579ce, Lean 4.30) | **2462/2469** nhưng tải đỉnh 35/8.5 | KHÔNG dùng làm số chứng nhận; nhưng vì tranh chấp chỉ gây âm tính giả, 2462 là **cận dưới năng lực thật** của build |
| 21/08 | Verify cộng-thêm (6 bài canh) | "giữ 1/3" ×3 lượt, đều đo trong tranh chấp | Báo động hồi quy GIẢ — bài học: đọc cờ môi trường trước khi tin phán quyết |
| 24/08 sáng | Ăn `hard2_0027` (cert vô hạn Austin đầu tiên) + `hard2_0125` (bảng ET00) | judge accepted, 2/2 qua pipeline | Hai bài "đã cạn mọi cách" đổ bằng năng lực mới từ ETP |
| 24/08 chiều | Merge upstream: **môi trường chấm đổi sang Lean/Mathlib 4.32.2** + judge vá 4 họ bypass | harness gate exit 0 (56 pipeline + 12 challenger case) | Mọi số cũ là đo trên môi trường khác thứ được chấm → phải đo lại |
| 24/08 chiều | Verify trên 4.32.2 | **6/6 accepted** (cờ NGỜ do tải dư từ harness) | Giải tỏa nghi án hồi quy theo hướng tốt |
| 24/08 chiều | Đối chứng bank: 1250 bài FALSE, có/không `ETP_TABLE_BANK` | **0 mất, 0 thêm, 1 đổi lộ trình** (`hard2_0051`, bảng không to hơn) | Bằng chứng cộng-thêm bằng số liệu, không bằng lý luận |
| 24/08 chiều | Kiểm oracle: toàn corpus | **2269/2269 khớp** (200 bài order-5 ngoài vũ trụ) | Oracle đáng tin để chia ngân sách |
| 24/08 tối | Baseline 4.32.2 (build d968874, container, 600 s, dừng chủ động theo chỉ đạo) | **2281/2284**, trượt đúng `hard3_0271/0314` + `order5_0014` | Không hồi quy toolchain; đúng hình trượt dự kiến |
| 24/08 đêm | Chấm 281 cert vô hạn (12 chiều) | **281/281 accepted** (sau khi sửa khuôn 1648b: 28 bài `rw` sai dạng `x+2` vs `x+1+1`) | Cơ sở để nhúng registry vào solver |
| 24/08 đêm | Máy lắp chuỗi: `hard3_0271` | chuỗi 2 bước, judge **accepted** | Tầng 3 chạy được thật; `hard3_0314` chưa xong |
| 25/08 rạng sáng | **Delta 191 bài** (184 đuôi chưa quét + 7 trượt cũ + 1 đổi lộ trình; qua measure.py, container, 600 s) | đang chạy | Thay cho re-sweep 2469 theo chỉ đạo; ledger cuối = 2284 dấu baseline + 191 dấu delta |

Logic hợp lệ của phép ghép ledger: build cuối chỉ khác baseline ở các thay
đổi cộng-thêm đã đối chứng — với mọi bài ngoài delta, chứng chỉ phát ra
**y hệt** baseline nên dấu judge cũ vẫn là dấu của đúng chứng chỉ đó; mọi
bài có thể khác (đuôi chưa quét, bài từng trượt, bài đổi lộ trình, bài lane
mới) đều nằm trong delta và mang dấu mới.

### Sự cố đêm 24–25/08 đã bắt và sửa (đáng ghi để khỏi tái phạm)

1. Bài con của máy chuỗi thiếu `eq1_id`/`eq2_id` → `is_reflexive_problem`
   so `None == None` → route reflexive `exact h` "chứng minh" mọi bước
   trong 0 giây. Cờ đỏ nhận diện: chứng chỉ 179 byte.
2. Header template vô hạn chứa token `Equation<số>` — bị chính
   `BANNED_LEAN_RE` của solver chặn (nó soi cả comment) → lane câm lặng,
   bài Austin rơi xuống saturation treo. Judge không cấm token này (281 cert
   accepted) — người chặn là chính mình. Đổi tên `ETP-<số>`.
3. Khuôn 1648b: `rw` cần `x + 1 + 1` (dạng goal thật) chứ không phải `x + 2`.

---

## Phần IV — Trạng thái điểm số và rủi ro mở

- Kỳ vọng ledger cuối: **≥ 2464/2469** trên corpus công khai (2462 cận dưới
  cũ + 2 bài hard2). `hard3_0271/0314` chỉ ăn được khi máy chuỗi vào solver
  (bước trượt 450 s không vừa khuôn đo 600 s, nhưng vừa 3600 s của giải
  thật). Ba bài order5 chờ delta phán.
- **Điểm thật nằm ở bộ đề riêng**: corpus công khai chỉ là proxy. Vũ khí cho
  đề riêng: kho bảng + oracle + lane vô hạn (đều độc lập với bài), và dư địa
  Order 5 vẫn là vùng rủi ro chính (ngoài vũ trụ ETP).
- Rủi ro mở: 190 cặp ngoại lệ oracle (nhịn, không sai); các cặp Austin thuộc
  họ greedy/noncomputable chưa phủ (~76 cặp); máy chuỗi chưa in-solver.
- Mốc: **đóng băng + nộp bản chắc 26/08 12:00 trưa (giờ VN)**; hạn nộp cuối
  31/08 23:59 AoE.
