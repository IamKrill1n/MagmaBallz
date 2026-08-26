#!/bin/bash
# DÂY CHUYỀN ĐO — chạy lại được, cô lập, tự khai báo môi trường.
#
# Gọi bao nhiêu lần cũng được: bỏ qua chặng đã xong, tiếp chặng dở. LaunchAgent
# com.magmaballz.chain gọi nó lúc đăng nhập và mỗi 10 phút.
#
#   bash .scratch/release/run_chain.sh          chạy/tiếp tục
#   bash .scratch/release/run_chain.sh status   chỉ xem
#
# MỌI phép đo đi qua .scratch/lab/measure.py — cửa duy nhất, cưỡng chế: máy
# phải sạch, độc quyền suốt lượt, cấu hình chuẩn (docker + Lean 120s + thư mục
# artifact riêng), và ghi dấu môi trường cạnh mỗi kết quả.
set -u
REPO=/Users/nhatminh/dev/active/MagmaBallz
S=/private/tmp/claude-501/-Users-nhatminh-dev-active-MagmaBallz/5aa77320-10be-4643-8ecb-555c1ad24f06/scratchpad
ML=$REPO/.scratch/ml
cd "$REPO"
source "$REPO/.env.judge" 2>/dev/null || true
# launchd khởi chạy với môi trường tối thiểu: thiếu DEVELOPER_DIR thì Lean rơi
# vào xcodebuild dò SDK và TREO VÔ HẠN; python3 phân giải sang bản hệ thống
# thiếu openai/sympy. Ghim cả hai.
export DEVELOPER_DIR="${DEVELOPER_DIR:-/Applications/Xcode.app/Contents/Developer}"
export PATH="$HOME/.elan/bin:/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:$PATH"
PY_BIN=/Library/Frameworks/Python.framework/Versions/3.11/bin/python3
[ -x "$PY_BIN" ] || PY_BIN="$(command -v python3)"
MEASURE="$PY_BIN $REPO/.scratch/lab/measure.py"
W=$("$PY_BIN" -c "import sys;sys.path.insert(0,'$REPO/.scratch/lab');import lab;print(lab.plan_workers())")

# --- dấu hoàn thành: kiểm NỘI DUNG, không kiểm mã thoát ------------------
done_verify()   { [ -f "$S/verify_additive.ledger.jsonl" ] &&
                  [ "$(grep -c '"judge": "accepted"' "$S/verify_additive.ledger.jsonl" 2>/dev/null)" -ge 6 ]; }
done_marathon() { grep -qiE "score|accuracy|solved" "$S/marathon_100.log" 2>/dev/null; }
done_sweep()    { [ -f "$S/results/final_cert.jsonl" ] &&
                  [ "$(wc -l < "$S/results/final_cert.jsonl")" -ge 2469 ]; }
done_sieve()    { grep -q "DONE:" "$S/sieve3.log" 2>/dev/null; }
done_harvest()  { grep -q "HARVEST DONE" "$ML/harvest.log" 2>/dev/null; }
done_census()   { grep -q "ROUTE CENSUS DONE" "$S/route_census.log" 2>/dev/null; }
done_label()    { grep -q "LABEL DOUBT DONE" "$S/label_doubt.log" 2>/dev/null; }

status() {
  for st in verify marathon sweep sieve harvest census label; do
    if done_$st; then printf "  [x] %s\n" "$st"; else printf "  [ ] %s\n" "$st"; fi
  done
}
[ "${1:-run}" = "status" ] && { echo "TRẠNG THÁI:"; status; exit 0; }

log() { echo "[$(date '+%m-%d %H:%M')] $*" | tee -a "$S/chain.log"; }

# --- khóa: launchd gọi lặp, chỉ MỘT lượt được chạy ------------------------
LOCKDIR="$S/.chain.lock"
if ! mkdir "$LOCKDIR" 2>/dev/null; then
  if [ -f "$LOCKDIR/pid" ] && kill -0 "$(cat "$LOCKDIR/pid")" 2>/dev/null; then exit 0; fi
  rm -rf "$LOCKDIR"; mkdir "$LOCKDIR" 2>/dev/null || exit 0
fi
echo $$ > "$LOCKDIR/pid"
trap 'rm -rf "$LOCKDIR"' EXIT INT TERM

log "=== dây chuyền: $W luồng (tính từ số lõi), build $(git rev-parse --short HEAD) ==="

# --- canh gác upstream: luật chấm điểm còn TBD, biết muộn là hỏng ---------
if git fetch sair --quiet 2>/dev/null; then
  NEW=$(git log --oneline HEAD..sair/main 2>/dev/null | wc -l | tr -d " ")
  [ "$NEW" != "0" ] && { log "  !! UPSTREAM CÓ $NEW COMMIT MỚI"; \
    git log --oneline HEAD..sair/main 2>/dev/null | head -5 | while read -r l; do log "     $l"; done; }
fi

gate() { log "  cổng $1: $("$PY_BIN" "$REPO/.scratch/release/check_stage.py" "$1" 2>&1 | head -1)"; }

# --- TẦNG 1-2: chặn nộp bài ----------------------------------------------
if ! done_verify; then
  [ -f "$S/verify_additive.ledger.jsonl" ] && mv "$S/verify_additive.ledger.jsonl" "$S/verify_additive.ledger.prev.jsonl"
  log "chặng 1: verify_additive"
  $MEASURE --name verify --result "$S/verify_additive.ledger.jsonl" --wait 7200 \
      -- "$PY_BIN" "$S/verify_additive.py" >> "$S/verify_additive.log" 2>&1
fi
gate verify

if ! done_marathon; then
  log "chặng 2: Marathon 99 bài"
  mkdir -p "$S/subs/m6marathon"; cp "$S/subs/m6final/solver.py" "$S/subs/m6marathon/solver.py"
  $MEASURE --name marathon --result "$S/marathon_100.log" --wait 7200 --reap-after 900 \
      -- "$PY_BIN" scripts/run_marathon.py --solver "$S/subs/m6marathon" \
         --manifest "$S/marathon_100.jsonl" > "$S/marathon_100.log" 2>&1
fi
gate marathon

if ! done_sweep; then
  log "chặng 3: sweep chứng nhận 2469 bài, trong container, $W luồng"
  # --reap-after: harness đặt hạn 600s/bài nhưng KHÔNG giết được container khi
  # solver bên trong không tự dừng — đo được một container sống 3 tiếng làm cả
  # lượt sweep đứng im ở 4/2469. Thu hồi sau 600+180s biên.
  # --solver-dir: chép build repo vào thư mục nộp bài RỒI khai mã băm ra dấu.
  # Sandbox gắn thư mục nộp bài, không phải file repo; ngày 21/08 cả 20 thư
  # mục nộp bài đều là bản cũ, phóng sweep lúc đó là đo nhầm build lặng lẽ.
  $MEASURE --name sweep --result "$S/results/final_cert.jsonl" --wait 7200 --reap-after 780 \
      --solver-dir "$S/subs/m6final" \
      -- "$PY_BIN" "$S/scoreboard.py" --solvers m6final \
         --corpora normal,hard1,hard2,hard3,evaluation_normal,evaluation_hard,evaluation_extra_hard,evaluation_order5 \
         --timeout 600 --workers "$W" --no-llm --tag final_cert > "$S/final_cert.log" 2>&1
fi
gate sweep

# --- TẦNG 3-5: chỉ chạy khi tầng trên xong -------------------------------
if done_verify && done_marathon && done_sweep; then
  if ! done_sieve; then
    log "chặng 4: sieve Forge"
    $MEASURE --name sieve --result "$S/sieve3.log" --wait 7200 \
        -- "$PY_BIN" "$REPO/.scratch/frontier-forge/forge_p2_sieve.py" > "$S/sieve3.log" 2>&1
  fi
  gate sieve
  if ! done_harvest; then
    log "chặng 5: harvest ML"
    $MEASURE --name harvest --result "$ML/train_rows.jsonl" --wait 7200 \
        -- "$PY_BIN" "$ML/harvest.py" > "$ML/harvest.log" 2>&1
  fi
  gate harvest
  if ! done_census; then
    log "chặng 6: census route"
    $MEASURE --name census --result "$S/route_census.log" --wait 7200 \
        -- "$PY_BIN" "$REPO/.scratch/release/route_census.py" > "$S/route_census.log" 2>&1
  fi
  gate census
  if ! done_label; then
    if [ -f "$S/label_doubt.py" ]; then
      log "chặng 7: label_doubt"
      $MEASURE --name label --result "$S/label_doubt.log" --wait 7200 \
          -- "$PY_BIN" "$S/label_doubt.py" >> "$S/label_doubt.log" 2>&1
    else
      # Bản gốc nằm trong scratchpad phiên 5aa77320 và đã bị dọn mất; đợt cứu
      # 25/08 không chép nó vào repo. Trước đây vòng lặp này im lặng chạy lại
      # một file không tồn tại mỗi 10 phút, mãi mãi — đúng họ lỗi số 5 của sổ
      # vận hành: "chạy mà không làm gì, trông như đang làm".
      log "chặng 7 BỎ QUA: thiếu $S/label_doubt.py (mất cùng scratchpad cũ) — phải viết lại trước khi chạy"
    fi
  fi
  gate label
else
  log "Tầng 3-5 tạm hoãn: còn chặng chặn nộp bài chưa xong"
fi

"$PY_BIN" "$REPO/.scratch/release/check_stage.py" all > /dev/null 2>&1
log "=== hoàn tất — xem .scratch/release/STATUS.md ==="
status
