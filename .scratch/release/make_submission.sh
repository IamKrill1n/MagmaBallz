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
git show $REF:SUBMISSION_NOTE.md > "$OUT/SUBMISSION_NOTE.md"
echo "$(git rev-parse $REF)" > "$OUT/BUILD_COMMIT.txt"

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
ls "$OUT" | grep -qx solver.py && say "một file solver.py duy nhất" "OK"
say "commit gốc" "$(cat $OUT/BUILD_COMMIT.txt | cut -c1-12)"
echo
[ $fail -eq 0 ] && echo "GÓI NỘP SẴN SÀNG: $OUT" || { echo "GÓI NỘP CÓ LỖI — KHÔNG NỘP"; exit 1; }
