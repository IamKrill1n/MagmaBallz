#!/bin/bash
# Dựng gói nộp TỪ MỘT COMMIT (không bao giờ từ file đang sửa) và tự kiểm.
# Dùng: bash .scratch/release/make_submission.sh [commit]  (mặc định HEAD)
set -e
REPO=/Users/nhatminh/dev/active/MagmaBallz
REF=${1:-HEAD}
OUT=$REPO/.scratch/release/submission
cd $REPO
rm -rf "$OUT"; mkdir -p "$OUT"
git show $REF:EQT02-M00006.py > "$OUT/solver.py"
# Ghi chú công bố và commit gốc KHÔNG được nằm cạnh solver.py.
# pipeline/proxy.py:575 và pipeline/marathon_runner.py:104 từ chối thư mục nộp
# có BẤT KỲ entry nào ngoài solver.py, và từ chối ở mức "chưa chạy solver" —
# tức là 0 điểm trong khi mã thoát vẫn 0. Đặt chúng ra thư mục anh em.
META="$(dirname "$OUT")/submission_meta"
mkdir -p "$META"
git show $REF:SUBMISSION_NOTE.md > "$META/SUBMISSION_NOTE.md"
echo "$(git rev-parse $REF)" > "$META/BUILD_COMMIT.txt"

fail=0
say() { printf "  %-46s %s\n" "$1" "$2"; }
BYTES=$(wc -c < "$OUT/solver.py")
[ "$BYTES" -le 512000 ] && say "kích thước $BYTES / 512000 B" "OK" || { say "kích thước $BYTES" "QUÁ HẠN MỨC"; fail=1; }
python3 -c "import ast,sys; ast.parse(open('$OUT/solver.py').read())" \
  && say "cú pháp Python" "OK" || { say "cú pháp Python" "LỖI"; fail=1; }
grep -q '^PROMPT' "$OUT/solver.py" && say "hằng PROMPT ở cấp module" "OK" || { say "hằng PROMPT" "THIẾU"; fail=1; }
python3 - "$OUT/solver.py" <<'PY'
import ast, sys
tree = ast.parse(open(sys.argv[1]).read())
mods = set()
for n in ast.walk(tree):
    if isinstance(n, ast.Import):
        mods |= {a.name.split('.')[0] for a in n.names}
    elif isinstance(n, ast.ImportFrom) and n.module and n.level == 0:
        mods.add(n.module.split('.')[0])
std = set(sys.stdlib_module_names) | {"marathon_llm"}
extra = sorted(mods - std)
print(f"  {'import ngoài thư viện chuẩn':<46} {extra if extra else 'KHÔNG CÓ — OK'}")
sys.exit(1 if extra else 0)
PY
[ $? -eq 0 ] || fail=1
# Phép kiểm cũ chỉ hỏi "có solver.py không", nên nó báo OK cho một gói có file
# thừa — đúng gói mà ban tổ chức sẽ từ chối. Nay hỏi "có gì NGOÀI solver.py không".
EXTRA=$(ls -A "$OUT" | grep -vx solver.py || true)
if [ -n "$EXTRA" ]; then
  say "chỉ mỗi solver.py trong thư mục nộp" "HỎNG — thừa: $(echo $EXTRA | tr '\n' ' ')"
  fail=1
else
  say "chỉ mỗi solver.py trong thư mục nộp" "OK"
fi
say "commit gốc" "$(cat $META/BUILD_COMMIT.txt | cut -c1-12)"
say "ghi chú công bố" "$META/SUBMISSION_NOTE.md"
echo
[ $fail -eq 0 ] && echo "GÓI NỘP SẴN SÀNG: $OUT" || { echo "GÓI NỘP CÓ LỖI — KHÔNG NỘP"; exit 1; }
