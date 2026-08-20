"""Phép thử bác bỏ RẺ: khớp một mô hình TUYẾN TÍNH trên chính bộ đặc trưng đó
và so với heuristic hiện tại (_gap_relevance) trên tập giữ lại.

Lý do làm cái này trước GBDT/GNN: nếu 24 đặc trưng quan hệ + hồi quy tuyến tính
KHÔNG thắng nổi heuristic thủ công, thì mô hình phức tạp hơn cũng sẽ không cứu —
và mình biết điều đó sau một ngày thay vì sau ba tuần.

Chỉ dùng thư viện chuẩn: gradient descent trên log-loss, không numpy.
"""
from __future__ import annotations
import json, math, pathlib, random, sys
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from features import FEATURE_NAMES

rows = [json.loads(l) for l in (HERE/"train_rows.jsonl").open() if l.strip()]
if not rows:
    print("chưa có dữ liệu — chạy harvest.py trước"); raise SystemExit(0)
# chia theo BÀI (không theo dòng) để không rò rỉ
pids = sorted({r["pid"] for r in rows})
random.Random(0).shuffle(pids)
cut = int(0.75*len(pids)); train_p = set(pids[:cut]); test_p = set(pids[cut:])
tr = [r for r in rows if r["pid"] in train_p]
te = [r for r in rows if r["pid"] in test_p]
D = len(FEATURE_NAMES)
# chuẩn hóa
mu = [sum(r["f"][j] for r in tr)/len(tr) for j in range(D)]
sd = [max(1e-6, (sum((r["f"][j]-mu[j])**2 for r in tr)/len(tr))**0.5) for j in range(D)]
def norm(f): return [(f[j]-mu[j])/sd[j] for j in range(D)]
w = [0.0]*D; b = 0.0
pos_w = max(1.0, sum(1 for r in tr if r["y"]==0)/max(1,sum(1 for r in tr if r["y"]==1)))
lr = 0.05
for epoch in range(60):
    random.Random(epoch).shuffle(tr)
    for r in tr:
        x = norm(r["f"]); z = sum(w[j]*x[j] for j in range(D)) + b
        p = 1/(1+math.exp(-max(-30,min(30,z))))
        g = (p - r["y"]) * (pos_w if r["y"]==1 else 1.0)
        for j in range(D): w[j] -= lr*g*x[j]
        b -= lr*g
def score(f): 
    x = norm(f); return sum(w[j]*x[j] for j in range(D)) + b
# ĐÁNH GIÁ ĐÚNG BÀI TOÁN: trong mỗi (bài, vòng), bổ đề dương có được xếp cao không?
gi = FEATURE_NAMES.index("gap_relevance")
groups = {}
for r in te: groups.setdefault((r["pid"], r["round"]), []).append(r)
def mean_rank(keyfn):
    rs = []
    for g in groups.values():
        if not any(r["y"] for r in g) or len(g) < 2: continue
        order = sorted(g, key=keyfn)
        for i, r in enumerate(order):
            if r["y"]:
                rs.append(i/max(1,len(g)-1)); break
    return (sum(rs)/len(rs) if rs else float("nan")), len(rs)
mr_ml, n = mean_rank(lambda r: -score(r["f"]))
mr_h, _  = mean_rank(lambda r: (-r["f"][gi], r["f"][FEATURE_NAMES.index("size_sum")]))
print(f"nhóm đánh giá: {n} | dòng train {len(tr)} test {len(te)}")
print(f"thứ hạng chuẩn hóa của bổ đề dương ĐẦU TIÊN (thấp = tốt):")
print(f"  heuristic hiện tại : {mr_h:.4f}")
print(f"  tuyến tính học được: {mr_ml:.4f}")
print(f"  => {'ML THẮNG' if mr_ml < mr_h else 'ML KHÔNG THẮNG'} ({(mr_h-mr_ml)/max(mr_h,1e-9)*100:+.1f}%)")
top = sorted(range(D), key=lambda j: -abs(w[j]))[:8]
print("đặc trưng nặng nhất:", [(FEATURE_NAMES[j], round(w[j],2)) for j in top])
