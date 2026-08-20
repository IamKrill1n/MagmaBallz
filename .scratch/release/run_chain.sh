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
  log "chặng 1: verify_additive"; python3 "$S/verify_additive.py" >> "$S/verify_additive.log" 2>&1 || true
fi
if ! done_marathon; then
  log "chặng 2: Marathon 99 bài (lần đầu)"
  mkdir -p "$S/subs/m6marathon"; cp "$S/subs/m6final/solver.py" "$S/subs/m6marathon/solver.py"
  python3 scripts/run_marathon.py --solver "$S/subs/m6marathon" \
      --manifest "$S/marathon_100.jsonl" > "$S/marathon_100.log" 2>&1 || true
fi
if ! done_sweep; then
  log "chặng 3: sweep chứng nhận 2469 bài"
  python3 "$S/scoreboard.py" --solvers m6final \
    --corpora normal,hard1,hard2,hard3,evaluation_normal,evaluation_hard,evaluation_extra_hard,evaluation_order5 \
    --timeout 120 --workers 3 --no-llm --tag final_cert > "$S/final_cert.log" 2>&1 || true
fi
if ! done_sieve; then
  log "chặng 4: sieve Forge (có sổ cái, tự resume)"
  python3 "$REPO/.scratch/frontier-forge/forge_p2_sieve.py" > "$S/sieve3.log" 2>&1 || true
fi
if ! done_harvest; then
  log "chặng 5: harvest ML (có sổ cái, tự resume)"
  python3 "$REPO/.scratch/ml/harvest.py" > "$REPO/.scratch/ml/harvest.log" 2>&1 || true
fi
if ! done_census; then
  log "chặng 6: census route"; python3 "$S/route_census.py" > "$S/route_census.log" 2>&1 || true
fi
if ! done_label; then
  log "chặng 7: label_doubt"; python3 "$S/label_doubt.py" >> "$S/label_doubt.log" 2>&1 || true
fi
log "=== dây chuyền hoàn tất ==="
status
