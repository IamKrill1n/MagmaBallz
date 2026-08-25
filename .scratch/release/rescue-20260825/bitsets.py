"""Tính bitset thỏa/phá: mỗi bảng x mỗi luật trong 4694 luật ETP.

Nền cho baseline 'bậc <=4 bất khả chiến bại': từ đây suy ra (a) độ phủ FALSE
trên TOÀN ma trận, (b) tập bảng tối tiểu để nhúng (set cover), (c) phần dư
phải xử bằng mô hình vô hạn (đối chiếu danh sách Austin).
Đo bằng numpy, vector hóa trọn từng cặp (luật, bảng)."""
import json, sys, time
import numpy as np
sys.path.insert(0,"/Users/nhatminh/dev/active/MagmaBallz")
import importlib.util
spec=importlib.util.spec_from_file_location("m6","/Users/nhatminh/dev/active/MagmaBallz/EQT02-M00006.py")
m6=importlib.util.module_from_spec(spec); spec.loader.exec_module(m6)
SPD="/private/tmp/claude-501/-Users-nhatminh-dev-active-MagmaBallz/5aa77320-10be-4643-8ecb-555c1ad24f06/scratchpad"

eqs=[]
for i,line in enumerate(open("/tmp/etp_equations.txt"),1):
    e=m6.parse_equation(line.strip().replace("◇","*"))
    eqs.append((i,e))
print(f"{len(eqs)} luật; phân bố số biến:", end=" ")
import collections
print(dict(sorted(collections.Counter(len(e['variables']) for _,e in eqs).items())), flush=True)

bang=[]
for f in ("/tmp/etp_4x4_tables.json","/tmp/etp_data_tables.json"):
    bang += json.load(open(f))
for k in json.load(open("/tmp/etp_fp_index.json")):
    n=k["n"]; ct=k["ct"]
    try: bang.append([[eval(ct,{"__builtins__":{}},{"x":i,"y":j})%n for j in range(n)] for i in range(n)])
    except Exception: pass
seen=set(); uniq=[]
for t in bang:
    key=json.dumps(t)
    if key not in seen: seen.add(key); uniq.append(t)
print(f"{len(uniq)} bảng khác nhau; bậc:", dict(sorted(collections.Counter(len(t) for t in uniq).items())), flush=True)

def eval_terms(term, grids, T):
    if term[0]=="var": return grids[term[1]]
    a=eval_terms(term[1],grids,T); b=eval_terms(term[2],grids,T)
    return T[a,b]

t0=time.time()
sat=np.zeros((len(uniq),len(eqs)),dtype=bool)
for ti,t in enumerate(uniq):
    n=len(t); T=np.array(t,dtype=np.int16)
    cache={}
    for ei,(num,e) in enumerate(eqs):
        vs=e["variables"]; v=len(vs)
        if (n,v) not in cache:
            cache[(n,v)]=np.meshgrid(*[np.arange(n)]*v, indexing="ij", sparse=True)
        gs=dict(zip(vs,cache[(n,v)]))
        try:
            L=eval_terms(e["lhs"],gs,T); R=eval_terms(e["rhs"],gs,T)
            sat[ti,ei]=bool(np.array_equal(L,R) if (np.shape(L)==np.shape(R)) else np.all(L==R))
        except Exception:
            sat[ti,ei]=False
    if ti%200==0:
        print(f"  {ti}/{len(uniq)} bảng  [{time.time()-t0:.0f}s]", flush=True)
np.save(SPD+"/etp_sat.npy", sat)
json.dump(uniq, open(SPD+"/etp_tables_uniq.json","w"))
print(f"XONG: ma trận thỏa {sat.shape}, {time.time()-t0:.0f}s", flush=True)
