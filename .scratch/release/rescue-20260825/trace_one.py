"""Chạy build của mình trên một bài và IN RA toàn bộ stderr — tức là nhật ký
route của solver. Câu hỏi: nó bỏ cuộc lúc nào, vì sao, endgame có chạy không."""
import json, os, pathlib, sys, time
REPO="/Users/nhatminh/dev/active/MagmaBallz"; sys.path.insert(0,REPO)
SPD="/private/tmp/claude-501/-Users-nhatminh-dev-active-MagmaBallz/5aa77320-10be-4643-8ecb-555c1ad24f06/scratchpad"
from pipeline.proxy import load_config, load_problems, run_solver
pid = sys.argv[1]; sub = sys.argv[2] if len(sys.argv)>2 else "m6final"
cfg = load_config(None); cfg["solver"]["timeout_seconds"]=600
if os.environ.get("SB_SANDBOX_MODE"): cfg["sandbox"]["mode"]=os.environ["SB_SANDBOX_MODE"]
p = next(q for q in load_problems(SPD+"/corpora/gap6.jsonl") if q["id"]==pid)
t0=time.time()
r = run_solver(pathlib.Path(SPD+"/subs/"+sub), p, cfg)
dt=time.time()-t0
print(f"=== {pid} / {sub}: giải={r.get('solved')} sau {dt:.1f}s "
      f"(ngân sách 600s) llm={r.get('llm_calls')} judge={r.get('judge_calls')} ===\n")
bits=[]
for e in r.get("log",[]):
    b=(e.get("tail") if e.get("type")=="solver_stderr" else None) \
       or e.get("stderr") or (e.get("response") or {}).get("stderr")
    if b: bits.append(str(b))
    if e.get("type")=="error": print("LỖI:", str(e.get("message"))[:300])
import collections
print("--- MỌI loại bản ghi trong log ---")
print(dict(collections.Counter(e.get("type") for e in r.get("log",[]))))
for e in r.get("log",[]):
    if e.get("type") not in ("llm","judge"):
        print("  ", {k:str(v)[:400] for k,v in e.items()})
blob="\n".join(bits)
print(f"--- nhật ký route của solver ({len(blob):,} ký tự) ---")
print(blob[-6000:] if blob else "(rỗng — proxy không giữ được stderr nào)")
