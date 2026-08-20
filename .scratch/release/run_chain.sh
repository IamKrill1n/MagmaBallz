#!/bin/bash
# DÂY CHUYỀN CÓ THỂ KHỞI ĐỘNG LẠI BẤT CỨ LÚC NÀO.
# Máy ngủ, tắt, sập nguồn, mất mạng -> chạy lại đúng lệnh này, nó tự bỏ qua
# những chặng đã xong và tiếp tục từ chặng dở. Mỗi chặng có dấu hoàn thành
# riêng; chặng nào có sổ cái thì tự resume bên trong.
#
#   bash .scratch/release/run_chain.sh          # chạy/tiếp tục
#   bash .scratch/release/run_chain.sh status   # chỉ xem trạng thái
set -u
REPO=/Users/nhatminh/dev/active/MagmaBallz
S=/private/tmp/claude-501/-Users-nhatminh-dev-active-MagmaBallz/5aa77320-10be-4643-8ecb-555c1ad24f06/scratchpad
cd "$REPO"; source "$REPO/.env.judge" 2>/dev/null || true
unset OPENAI_API_KEY OPENROUTER_API_KEY

# launchd khởi chạy với môi trường TỐI THIỂU, khác hẳn terminal. Lean gọi
# trình biên dịch C, và nếu thiếu DEVELOPER_DIR thì nó rơi vào `xcodebuild`
# dò SDK — lệnh này TREO VÔ HẠN dưới launchd (đo được: kẹt 3'39 ở 0% CPU và
# chặn cả dây chuyền). Đặt tường minh, không để nó tự dò.
export DEVELOPER_DIR="${DEVELOPER_DIR:-/Applications/Xcode.app/Contents/Developer}"
# judge gọi `lake env` mỗi lần verify để lấy LEAN_PATH, timeout 30s — dưới
# launchd/khi máy bận thì lệnh đó QUÁ GIỜ và cả chặng chết. Framework có sẵn
# cửa thoát: JUDGE_LEAN_PATH nạp sẵn thì nó bỏ qua lake hoàn toàn.
[ -f "$REPO/.scratch/release/lean_path.txt" ] && \
  export JUDGE_LEAN_PATH="$(cat "$REPO/.scratch/release/lean_path.txt")"
export SDKROOT="${SDKROOT:-$(xcrun --sdk macosx --show-sdk-path 2>/dev/null || true)}"
export PATH="$HOME/.elan/bin:/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:$PATH"

# launchd phân giải python3 sang Python HỆ THỐNG, thiếu openai/sympy mà
# pipeline cần -> ghim đúng trình thông dịch tương tác.
PY_BIN="/Library/Frameworks/Python.framework/Versions/3.11/bin/python3"
[ -x "$PY_BIN" ] || PY_BIN="$(command -v python3)"

# Mọi chặng chạy dưới `timeout`: một chặng treo chỉ mất chặng đó, không bao
# giờ chặn dây chuyền. Lần gọi sau của launchd sẽ thử lại chặng dở.
run_stage() { timeout "$1" "${@:2}"; rc=$?; [ $rc -eq 124 ] && log "  !! chặng quá giờ ${1}, sẽ thử lại lượt sau"; return 0; }

# CỔNG CHẤT LƯỢNG: sau mỗi chặng, hỏi "kết quả có hợp lý không" chứ không hỏi
# "có chạy không". Kết luận ghi vào STATUS.md để người/session sau đọc được.
gate() {
  local v
  v=$("$PY_BIN" "$REPO/.scratch/release/check_stage.py" "$1" 2>&1 | head -1)
  log "  cổng $1: $v"
  case "$v" in *"HỎNG"*) log "  ⛔ CHẶN NỘP — $1 hỏng, xem STATUS.md" ;; esac
}

done_verify()   { grep -q "VERIFY ADDITIVE DONE" "$S/verify_additive.log" 2>/dev/null; }
done_marathon() { grep -qiE "score|accuracy|solved" "$S/marathon_100.log" 2>/dev/null; }
done_sweep()    { [ -f "$S/results/final_cert.jsonl" ] && [ "$(wc -l < "$S/results/final_cert.jsonl")" -ge 2469 ]; }
done_sieve()    { grep -q "DONE:" "$S/sieve3.log" 2>/dev/null; }
done_harvest()  { grep -q "HARVEST DONE" "$REPO/.scratch/ml/harvest.log" 2>/dev/null; }
done_census()   { grep -q "ROUTE CENSUS DONE" "$S/route_census.log" 2>/dev/null; }
done_label()    { grep -q "LABEL DOUBT DONE" "$S/label_doubt.log" 2>/dev/null; }

status() {
  for st in verify marathon sweep sieve harvest census label; do
    if done_$st; then printf "  [x] %s\n" "$st"; else printf "  [ ] %s\n" "$st"; fi
  done
}
[ "${1:-run}" = "status" ] && { echo "TRẠNG THÁI DÂY CHUYỀN:"; status; exit 0; }

log() { echo "[$(date '+%m-%d %H:%M')] $*" | tee -a "$S/chain.log"; }

# Khóa: launchd gọi lặp lại, chỉ cho phép MỘT lượt chạy tại một thời điểm.
# mkdir là thao tác nguyên tử trên mọi hệ tệp -> không cần flock.
LOCKDIR="$S/.chain.lock"
if ! mkdir "$LOCKDIR" 2>/dev/null; then
  if [ -f "$LOCKDIR/pid" ] && kill -0 "$(cat "$LOCKDIR/pid")" 2>/dev/null; then
    exit 0                      # lượt trước còn sống -> im lặng thoát
  fi
  rm -rf "$LOCKDIR"; mkdir "$LOCKDIR" 2>/dev/null || exit 0   # khóa mồ côi sau khi mất điện
fi
echo $$ > "$LOCKDIR/pid"
trap 'rm -rf "$LOCKDIR"' EXIT INT TERM

log "=== dây chuyền khởi động/tiếp tục ==="
if ! done_verify; then
  log "chặng 1: verify_additive"; run_stage 2h "$PY_BIN" "$S/verify_additive.py" >> "$S/verify_additive.log" 2>&1
fi
gate verify
if ! done_marathon; then
  log "chặng 2: Marathon 99 bài (lần đầu)"
  mkdir -p "$S/subs/m6marathon"; cp "$S/subs/m6final/solver.py" "$S/subs/m6marathon/solver.py"
  run_stage 3h "$PY_BIN" scripts/run_marathon.py --solver "$S/subs/m6marathon" \
      --manifest "$S/marathon_100.jsonl" > "$S/marathon_100.log" 2>&1
fi
gate marathon
if ! done_sweep; then
  log "chặng 3: sweep chứng nhận 2469 bài"
  # SWEEP CHẠY TRÊN HỆ THỐNG THẬT, không mô phỏng: solver chạy TRONG container
  # ee-solver (2 CPU, 2GB, không mạng, non-root, chỉ đọc) đúng như ban tổ chức
  # chấm, chứ không phải trên máy trần. Ngân sách 600s mỗi bài.
  # Khói 6 bài trước: docker hỏng thì bỏ lượt chứ không đốt nhiều giờ vô ích.
  # Gốc artifact riêng cho lượt sweep này: judge đặt tên thư mục theo băm
  # (bài + đáp án), nên dùng lại gốc cũ là kế thừa trạng thái build của lượt
  # trước — đã đo được nó biến `accepted` thành `incorrect`.
  export JUDGE_ARTIFACT_DIR="/private/tmp/mb-sweep-artifacts-$(date +%s)"
  mkdir -p "$JUDGE_ARTIFACT_DIR"
  export SB_SANDBOX_MODE=docker
  log "  khói docker 6 bài"
  if ! timeout 40m "$PY_BIN" "$S/scoreboard.py" --solvers m6final --corpora hard1 \
        --sample 6 --timeout 600 --workers 2 --no-llm --tag docker_smoke \
        > "$S/docker_smoke.log" 2>&1; then
    log "  !! khói docker HỎNG — bỏ lượt sweep, xem docker_smoke.log"
    unset SB_SANDBOX_MODE
  else
  run_stage 24h "$PY_BIN" "$S/scoreboard.py" --solvers m6final \
    --corpora normal,hard1,hard2,hard3,evaluation_normal,evaluation_hard,evaluation_extra_hard,evaluation_order5 \
    --timeout 600 --workers 3 --no-llm --tag final_cert > "$S/final_cert.log" 2>&1
  unset SB_SANDBOX_MODE
  rm -rf "$JUDGE_ARTIFACT_DIR"; unset JUDGE_ARTIFACT_DIR
  fi
fi
gate sweep
# LUẬT ƯU TIÊN: các chặng Tầng 3-5 CHỈ chạy khi Tầng 1-2 xong. Nếu không,
# một chặng Tầng 2 bị gián đoạn sẽ phải xếp hàng sau nhiều giờ việc phụ —
# đúng chuyện vừa xảy ra khi sweep bị dừng giữa chừng.
if done_verify && done_marathon && done_sweep; then

if ! done_sieve; then
  log "chặng 4: sieve Forge (có sổ cái, tự resume)"
  run_stage 4h "$PY_BIN" "$REPO/.scratch/frontier-forge/forge_p2_sieve.py" > "$S/sieve3.log" 2>&1
fi
gate sieve
if ! done_harvest; then
  log "chặng 5: harvest ML (có sổ cái, tự resume)"
  run_stage 2h "$PY_BIN" "$REPO/.scratch/ml/harvest.py" > "$REPO/.scratch/ml/harvest.log" 2>&1
fi
gate harvest
if ! done_census; then
  log "chặng 6: census route"; run_stage 3h "$PY_BIN" "$S/route_census.py" > "$S/route_census.log" 2>&1
fi
gate census
if ! done_label; then
  log "chặng 7: label_doubt"; run_stage 3h "$PY_BIN" "$S/label_doubt.py" >> "$S/label_doubt.log" 2>&1
fi
gate label

else
  log "Tầng 3-5 tạm hoãn: còn chặng chặn nộp bài chưa xong"
fi
"$PY_BIN" "$REPO/.scratch/release/check_stage.py" all > /dev/null 2>&1
log "=== dây chuyền hoàn tất — xem .scratch/release/STATUS.md ==="
status