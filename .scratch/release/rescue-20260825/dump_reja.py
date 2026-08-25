"""Chạy một solver trên bộ 6 bài chênh lệch và LƯU LẠI chứng chỉ Lean nó phát ra.
Chứng chỉ là thứ khai ra kỹ thuật: hình dạng chứng minh nói động cơ nó làm gì."""
import json, os, pathlib, sys, time
REPO="/Users/nhatminh/dev/active/MagmaBallz"; sys.path.insert(0,REPO)
SPD="/private/tmp/claude-501/-Users-nhatminh-dev-active-MagmaBallz/5aa77320-10be-4643-8ecb-555c1ad24f06/scratchpad"
from pipeline.proxy import load_config, load_problems, run_solver
sub = sys.argv[1] if len(sys.argv)>1 else "reja23"
cfg = load_config(None); cfg["solver"]["timeout_seconds"]=600
if os.environ.get("SB_SANDBOX_MODE"): cfg["sandbox"]["mode"]=os.environ["SB_SANDBOX_MODE"]
out = pathlib.Path(SPD+f"/certs_{sub}"); out.mkdir(exist_ok=True)
for p in load_problems(SPD+"/corpora/gap6.jsonl"):
    t0=time.time()
    r = run_solver(pathlib.Path(SPD+"/subs/"+sub), p, cfg)
    codes=[]
    for e in r.get("log",[]):
        if e.get("type")=="judge":
            c=(e.get("request") or {}).get("code")
            if c: codes.append((c,(e.get("response") or {}).get("status")))
    print(f"{p['id']:<26} giải={'CÓ' if r.get('solved') else 'không':<6} "
          f"llm={r.get('llm_calls')} judge={r.get('judge_calls')} {time.time()-t0:.0f}s", flush=True)
    for i,(c,st) in enumerate(codes):
        f=out/f"{p['id']}.{i}.{st}.lean"; f.write_text(c)
        print(f"    -> {f.name}  ({len(c):,} byte)", flush=True)
