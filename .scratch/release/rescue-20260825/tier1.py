"""TẦNG 1 — đo trước, xây sau.

Hai câu hỏi, cả hai đo bằng đại lượng TẤT ĐỊNH (số nút / đơn vị công) chứ
không bằng giây, nên máy có bị Ollama giành CPU thì kết quả vẫn y nguyên,
chỉ chậm đồng hồ treo tường.

A. Phía FALSE: bộ tìm mô hình có thấy phản mẫu ở bậc 7..12 không, nếu được
   cấp ngân sách thật? (Hiện bị hạn nội bộ 12 giây chặn cứng: hard_deadline
   = min(own_deadline, deadline), nên hạn ngoài truyền vào là vô nghĩa.)

B. Phía TRUE: động cơ bão hòa có dựng nổi cầu sập không, ở đúng slack mà
   endgame dùng (26 và 32), nếu được cấp công thật thay vì 15 giây mỗi nấc?
"""
import importlib.util, json, sys, time
REPO="/Users/nhatminh/dev/active/MagmaBallz"; sys.path.insert(0,REPO)
SPD="/private/tmp/claude-501/-Users-nhatminh-dev-active-MagmaBallz/5aa77320-10be-4643-8ecb-555c1ad24f06/scratchpad"
spec=importlib.util.spec_from_file_location("m6",REPO+"/EQT02-M00006.py")
m6=importlib.util.module_from_spec(spec); spec.loader.exec_module(m6)
probs={json.loads(l)["id"]:json.loads(l) for l in open(SPD+"/corpora/fail7.jsonl")}
FALSE=[p for p,q in probs.items() if q.get("answer") is False]
TRUE =[p for p,q in probs.items() if q.get("answer") is True]

print("="*78); print("A. PHÍA FALSE — tìm phản mẫu bậc 4..12, ngân sách thật")
print("="*78, flush=True)
m6.BACKTRACK_TIME_BUDGET = 1e9                       # bỏ hạn nội bộ 12s
m6.BACKTRACK_NODE_CAPS = {n: 3_000_000 for n in range(4,13)}
for pid in sorted(FALSE):
    q=probs[pid]
    e1=m6.parse_equation(q["equation1"].replace("◇","*"))
    e2=m6.parse_equation(q["equation2"].replace("◇","*"))
    print(f"\n{pid}  (H: {q['equation1']}   G: {q['equation2']})", flush=True)
    for n in range(4,13):
        t0=time.time()
        r=m6.backtracking_countermodel(e1,e2,sizes=(n,),
                                       deadline=time.monotonic()+900)
        dt=time.time()-t0
        print(f"   bậc {n:>2}: {'TÌM ĐƯỢC PHẢN MẪU ***' if r else 'không có'}"
              f"   {dt:7.1f}s   (nắp 3M nút)", flush=True)
        if r: break

print("\n"+"="*78); print("B. PHÍA TRUE — dựng cầu sập, slack 26 và 32, ngân sách công thật")
print("="*78, flush=True)
for pid in sorted(TRUE):
    q=probs[pid]
    e1=m6.parse_equation(q["equation1"].replace("◇","*"))
    print(f"\n{pid}  (H: {q['equation1']})", flush=True)
    mods=m6.find_h_models(e1)
    for rung in m6.HEAVY_LADDER_RUNGS:
        re_=m6.parse_equation(rung.replace("◇","*"))
        if any(not m6.table_satisfies_equation(re_,t) for t in mods):
            print(f"   nấc {rung:<12} H có mô hình phá nấc -> loại (đúng)", flush=True)
            continue
        for slack in (26, 32):
            sr=[]; t0=time.time()
            r=m6._cp_saturation_attempt(e1, re_, lemma_budget=6000, rounds=400,
                deadline=time.monotonic()+1800, beam=False, term_slack=slack,
                raw_pair_cap=600*slack, gap_time=60.0,
                work_budget=3_000_000, stop_reason=sr)
            print(f"   nấc {rung:<12} slack {slack}: "
                  f"{'DỰNG ĐƯỢC ***' if r else 'không dựng được'}"
                  f"   dừng vì={sr[-1] if sr else '?'}   {time.time()-t0:7.1f}s", flush=True)
            if r: break
        if r: break
print("\nXONG.", flush=True)
