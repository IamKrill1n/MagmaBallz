"""Thu hoạch dữ liệu huấn luyện từ chính chứng minh của solver.

Phương pháp ENIGMA, nhưng nguồn là trace của CHÍNH engine mình nên nhãn nằm
đúng calculus (không phải calculus của Vampire/E) và đúng phân bố đề thật.

Nhãn dương: bổ đề CÓ MẶT trong tập cited của chứng minh cuối cùng.
Nhãn âm  : bổ đề đã vào pool nhưng KHÔNG được trích dẫn.
Ghi ra JSONL: {"f": [...24 đặc trưng...], "y": 0|1, "pid": ..., "round": n}
"""
from __future__ import annotations
import importlib.util, json, pathlib, sys, time

HERE = pathlib.Path(__file__).resolve().parent
REPO = pathlib.Path("/Users/nhatminh/dev/active/MagmaBallz")
# Bộ đề delta của phiên đo cũ: đường /private/tmp đã bị dọn, bản cứu nằm
# trong repo. Glob trên thư mục không tồn tại trả về rỗng — nghĩa là trước
# vá này harvest lặng lẽ bỏ qua toàn bộ corpora delta mà không báo gì.
SCRATCH = REPO / ".scratch/release/rescue-20260825"
sys.path.insert(0, str(HERE))
import features as F

spec = importlib.util.spec_from_file_location("m6", REPO / "EQT02-M00006.py")
m6 = importlib.util.module_from_spec(spec); spec.loader.exec_module(m6)

OUT = HERE / "train_rows.jsonl"
LEDGER = HERE / "harvested_ids.txt"
done = set(LEDGER.read_text().split()) if LEDGER.exists() else set()

probs, seen = [], set()
for f in sorted(SCRATCH.glob("corpora/*.jsonl")) + sorted((REPO/"examples/problems").glob("*.jsonl")):
    for line in f.open():
        try: p = json.loads(line)
        except Exception: continue
        if "equation1" in p and p.get("answer") is True and p["id"] not in seen:
            seen.add(p["id"]); probs.append(p)
# ưu tiên băng yếu: order5 và hard2 trước (Amendment 4)
def band(p):
    i = p["id"]
    return (0 if "order5" in i else 1 if i.startswith("hard2") else
            2 if i.startswith("hard3") else 3)
probs.sort(key=lambda p: (band(p), p["id"]))

out = OUT.open("a"); led = LEDGER.open("a")
n_pos = n_neg = n_prob = 0
t_start = time.time()
for p in probs:
    if p["id"] in done: continue
    if time.time() - t_start > 5400: break        # trần 90 phút mỗi lượt
    try:
        eq1 = m6.parse_equation(p["equation1"].replace("◇", "*"))
        eq2 = m6.parse_equation(p["equation2"].replace("◇", "*"))
    except Exception: continue
    # bắt pool từng vòng
    rounds = []
    orig = m6.derive_gap_lemmas
    def dw(e1, pool, src, dst, **kw):
        got = orig(e1, pool, src, dst, **kw)
        rounds.append((src, dst, [dict(g) for g in got]))
        return got
    m6.derive_gap_lemmas = dw
    try:
        r = m6._cp_saturation_attempt(eq1, eq2, lemma_budget=1500, rounds=40,
                                      deadline=time.monotonic()+45, beam=False,
                                      term_slack=20, raw_pair_cap=8000, gap_time=8.0)
    except Exception:
        r = None
    finally:
        m6.derive_gap_lemmas = orig
    if r is None or not rounds: 
        led.write(p["id"] + "\n"); led.flush(); continue
    _tag, _proof, cited = r
    cited_names = {c["name"] for c in cited}
    depth_of = {}
    for _s, _d, got in rounds:
        for g in got:
            depth_of[g["name"]] = 1 + max((depth_of.get(c, 0) for c in g.get("cites", ())), default=0)
    for ri, (src, dst, got) in enumerate(rounds):
        for g in got:
            y = 1 if g["name"] in cited_names else 0
            try:
                f = F.extract(m6, g, src, dst, eq1, deriv_depth=depth_of.get(g["name"], 0))
            except Exception: continue
            out.write(json.dumps({"f": f, "y": y, "pid": p["id"], "round": ri}) + "\n")
            n_pos += y; n_neg += 1 - y
    n_prob += 1
    led.write(p["id"] + "\n"); led.flush(); out.flush()
    if n_prob % 20 == 0:
        print(json.dumps({"bài": n_prob, "dương": n_pos, "âm": n_neg}), flush=True)
print(json.dumps({"XONG_LUOT": n_prob, "dương": n_pos, "âm": n_neg}), flush=True)
print("HARVEST DONE", flush=True)
