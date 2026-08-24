# Hàng mang về từ Equational Theories Project (teorth/equational_theories)

Kéo về ngày 24/08/2026. Mã số phương trình của đề thi CHÍNH LÀ hệ số ETP —
đã xác minh 8/8 phương trình bậc 4 khớp nguyên văn với data/equations.txt.

## Phản mẫu VÔ HẠN cho hard2_0027 (eq1167 ⇏ eq1763) — cặp Austin

`Equation1659.lean` (7.107 byte, nguyên văn từ equational_theories/ManuallyProved/).
Cặp 1167→1763 nằm dòng 228 của Austin_implications.txt: đúng với MỌI magma
hữu hạn, chỉ sai ở magma vô hạn — nên mọi tìm kiếm bảng hữu hạn đều vô vọng
về nguyên lý.

Chuỗi suy luận (tự dựng lại từ outcomes 2024-11-10, không có sẵn trong kho):
  M = (ℕ, op_1659_4315) ⊨ 1659, và 1659 ⇒ 2473, nên M ⊨ 2473
  M ⊭ Y với các Y mà 1852 ⇒ Y, nên M ⊭ 1852
  => M chứng kiến 2473 ⇏ 1852
  Đối ngẫu (đảo hai đối số): M* chứng kiến dual(2473)=1167 ⇏ dual(1852)=1763

Phép toán, viết cho bài mình (M* = đảo đối số của op ETP):
  x ◇ y  =  op(y, x)   với   op(0,t) = 1 nếu t chẵn, 0 nếu lẻ
                              op(n+1,t) = n+2 nếu (n+1)≡t (mod 2), n nếu khác

ĐÃ KIỂM SỐ HỌC 24/08: M* thỏa eq1167 trên toàn [0,60)³; phá eq1763 tại
(x,y,z)=(0,1,0) — 32 bộ vi phạm trong [0,8)³.

Việc còn lại để ăn điểm: viết chứng chỉ Lean tự chứa ≤ 20 KB (nắp
MAX_FALSE_CERT_BYTES) dưới ALLOWED_IMPORTS của judge. Bản gốc dùng
omega/simp/decide + import Mathlib — cần kiểm tương thích.

## Kho bảng hữu hạn (phủ 99% mọi bài FALSE của corpus, kiểm trong 2 giây)

- all4x4_tables.json      940 bảng từ Generated/All4x4Tables/Refutation*.lean
                          (bậc 2..65; nguồn: brute-force C, Mace4, Z3, Vampire)
- data_tables.json        2280 bảng từ Generated/All4x4Tables/data/*.txt
- finitepoly_index.json   132 magma đa thức (Fin 2..5) kèm danh sách thỏa/phá
                          — dạng BẬC HAI (x²+y²…), thứ tầng affine mình không sinh

Phản mẫu bậc 6 cho hard2_0125 lấy từ all4x4_tables: judge đã ACCEPTED
(337 byte, 9 giây) — xem hard2_0125_witness.json trong scratchpad phiên.

- Austin_implications.txt 820 cặp "đúng hữu hạn, sai tổng quát" — gặp bài
                          nào trong danh sách này thì ĐỪNG đốt ngân sách tìm
                          bảng hữu hạn.
