"""Hiệu chuẩn: bao nhiêu byte cho mỗi ô cache memo?

Cần con số này vì trên macOS không có cgroup, nên chốt bộ nhớ phải đo bằng
một đại lượng ĐỎ ĐƯỢC Ở MỌI NƠI. Tổng số ô trong 12 cache là ứng viên: nó
đếm được không cần cgroup, không cần RSS, và KHÔNG phụ thuộc tải máy — nên
phép đo dùng nó là tất định, đúng nguyên tắc đo-bằng-công.
"""
import importlib.util, json, os, subprocess, sys, threading, time
REPO="/Users/nhatminh/dev/active/MagmaBallz"; sys.path.insert(0,REPO)
SPD="/private/tmp/claude-501/-Users-nhatminh-dev-active-MagmaBallz/5aa77320-10be-4643-8ecb-555c1ad24f06/scratchpad"
spec=importlib.util.spec_from_file_location("m6",REPO+"/EQT02-M00006.py")
m6=importlib.util.module_from_spec(spec); spec.loader.exec_module(m6)

def cache_entries():
    tot=0
    for obj in vars(m6).values():
        ci=getattr(obj,"cache_info",None)
        if callable(ci):
            try: tot+=ci().currsize
            except Exception: pass
    return tot

def rss_mb():
    out=subprocess.run(["ps","-o","rss=","-p",str(os.getpid())],
                       capture_output=True,text=True).stdout.strip()
    return int(out or 0)/1024

probs={json.loads(l)["id"]:json.loads(l) for l in open(SPD+"/corpora/gap6.jsonl")}
q=probs["evaluation_order5_0016"]
e1=m6.parse_equation(q["equation1"].replace("◇","*"))
rung=m6.parse_equation("x = y")

stop=threading.Event(); rows=[]
def watch():
    t0=time.time()
    while not stop.wait(4.0):
        r,c=rss_mb(),cache_entries()
        rows.append((time.time()-t0,r,c))
        print(f"  {time.time()-t0:6.0f}s  RSS {r:8.0f} MB  ô cache {c:12,}  "
              f"byte/ô {(r*1048576/c if c else 0):8.0f}", flush=True)
        if r > 3500:
            print("  >>> DỪNG: RSS vượt 3,5 GB, không đẩy máy xa hơn", flush=True)
            os._exit(0)
threading.Thread(target=watch,daemon=True).start()
m6._cp_saturation_attempt(e1, rung, lemma_budget=4000, rounds=200,
    deadline=time.monotonic()+420, beam=False, term_slack=26,
    raw_pair_cap=600*26, gap_time=30.0)
stop.set(); time.sleep(0.1)
if rows:
    r,c=rows[-1][1],rows[-1][2]
    print(f"\nKẾT LUẬN: {r*1048576/c if c else 0:.0f} byte mỗi ô cache "
          f"(mẫu cuối: {r:.0f} MB / {c:,} ô)")
