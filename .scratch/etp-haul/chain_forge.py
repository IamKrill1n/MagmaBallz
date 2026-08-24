# MÁY LẮP CHUỖI (tầng 3): biến "TRUE implicit" của ETP thành chứng chỉ Lean.
#
# Với bài TRUE (E1 => E2) mà engine không đánh được cú nhảy tổng:
#   1. Tìm đường lớp C(E1) -> ... -> C(E2) trên đồ thị Hasse (BFS, mọi đường
#      ngắn nhất, thử lần lượt).
#   2. Mỗi bước lớp: chọn vài phương trình đại diện (ưu tiên cỡ nhỏ), nhờ
#      ENGINE của solver chứng minh bước A => B như một bài con.
#   3. Ghép: have h1 := <thân bước 1 dùng h0>; ... ; exact hk.
# Mỗi thân bước lấy từ chứng chỉ do solver phát cho bài con (đã tuân thủ
# chính sách judge sẵn), nên chuỗi ghép cũng tuân thủ.
#
#   python3 chain_forge.py hard3_0271 hard3_0314      # thử các bài nêu tên
import importlib.util
import json
import pathlib
import pickle
import sys
import time
from collections import deque

HERE = pathlib.Path(__file__).parent
REPO = HERE.parent.parent

spec = importlib.util.spec_from_file_location("solver", REPO / "EQT02-M00006.py")
solver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(solver)

EQ_TEXT = [l.strip() for l in open(HERE / "equations.txt", encoding="utf-8")]
ORACLE = pickle.load(open(HERE / "oracle.pkl", "rb"))
CLS, HASSE, CREACH = ORACLE["cls"], ORACLE["hasse"], ORACLE["creach"]
N_CLS = len(CREACH)
ADJ = [[] for _ in range(N_CLS)]
for a, b in HASSE:
    ADJ[a].append(b)
MEMBERS = [[] for _ in range(N_CLS)]
for eq_id, c in enumerate(CLS, start=1):
    MEMBERS[c].append(eq_id)
for c in range(N_CLS):
    MEMBERS[c].sort(key=lambda i: len(EQ_TEXT[i - 1]))

STEP_PREFIX = "import JudgeProblem\n\ndef submission : Goal := by\n  intro G _ h\n"
MAX_CANDIDATES_PER_CLASS = 3
STEP_TIME_NOTE = 240.0  # engine tự giới hạn qua lemma budget; đây chỉ để log


def class_paths(src_cls, dst_cls, limit=6):
    """Mọi đường ngắn nhất src->dst trên Hasse (tối đa `limit` đường)."""
    if src_cls == dst_cls:
        return [[src_cls]]
    parents = {src_cls: []}
    depth = {src_cls: 0}
    q = deque([src_cls])
    found_depth = None
    while q:
        u = q.popleft()
        if found_depth is not None and depth[u] >= found_depth:
            continue
        for v in ADJ[u]:
            if v not in depth:
                depth[v] = depth[u] + 1
                parents[v] = [u]
                q.append(v)
            elif depth[v] == depth[u] + 1:
                parents[v].append(u)
            if v == dst_cls and found_depth is None:
                found_depth = depth[v]
    if dst_cls not in parents:
        return []
    paths = []

    def walk(node, acc):
        if len(paths) >= limit:
            return
        if node == src_cls:
            paths.append([src_cls] + acc)
            return
        for p in parents[node]:
            walk(p, [node] + acc)

    walk(dst_cls, [])
    return paths


_STEP_FAILED: set[tuple[str, str]] = set()


def prove_step(a_text, b_text):
    """Nhờ engine chứng minh A => B; trả về thân tactic (đã bỏ header) hoặc None."""
    if a_text == b_text:
        return None
    if (a_text, b_text) in _STEP_FAILED:
        return None
    # eq id giả PHÂN BIỆT — thiếu chúng thì is_reflexive_problem so
    # None == None và route reflexive bắn `exact h` bừa cho mọi bước.
    problem = {"id": "step", "eq1_id": -1, "eq2_id": -2,
               "equation1": a_text, "equation2": b_text}
    try:
        out = solver.solve_problem(problem, false_time_budget=0.5)
    except Exception:
        return None
    if not out or out["answer"]["verdict"] != "true":
        _STEP_FAILED.add((a_text, b_text))
        return None
    code = out["answer"]["code"]
    if not code.startswith(STEP_PREFIX):
        _STEP_FAILED.add((a_text, b_text))
        return None  # khuôn lạ (reflexive/singleton...) — bỏ cho an toàn
    body = code[len(STEP_PREFIX):]
    return body.rstrip() + "\n", out["route"]


def forall_stmt(eq):
    vs = " ".join(eq["variables"])
    lhs = solver.term_to_lean(eq["lhs"])
    rhs = solver.term_to_lean(eq["rhs"])
    return f"∀ {vs} : G, {lhs} = {rhs}"


def assemble(chain_bodies, stmts):
    lines = ["import JudgeProblem", "", "def submission : Goal := by",
             "  intro G _ h0"]
    for i, (body, stmt) in enumerate(zip(chain_bodies, stmts), start=1):
        lines.append(f"  have h{i} : {stmt} := by")
        lines.append(f"    have h := h{i - 1}")
        for ln in body.splitlines():
            lines.append("  " + ln if ln.strip() else ln)
    lines.append(f"  exact h{len(chain_bodies)}")
    return "\n".join(lines) + "\n"


def forge(problem):
    eq1 = solver.parse_equation(problem["equation1"])
    eq2 = solver.parse_equation(problem["equation2"])
    assert solver._etp_oracle_init()
    st = solver._ETP_ORACLE_STATE
    i = st["canon2id"].get(solver.alpha_canonical_pair(eq1))
    j = st["canon2id"].get(solver.alpha_canonical_pair(eq2))
    if not i or not j:
        print("  ngoài vũ trụ — máy chuỗi không áp dụng")
        return None
    c1, c2 = CLS[i - 1], CLS[j - 1]
    paths = class_paths(c1, c2)
    print(f"  lớp {c1} -> {c2}: {len(paths)} đường ngắn nhất, "
          f"dài {len(paths[0]) - 1 if paths else '-'} bước")
    # biến thể phía nguồn: None = dùng E1 thẳng; hoặc hop nội-lớp sang dạng
    # tương đương của giả thuyết trước khi nhảy.
    src_variants = [None] + [
        EQ_TEXT[m - 1] for m in MEMBERS[c1][:MAX_CANDIDATES_PER_CLASS]
        if EQ_TEXT[m - 1] != problem["equation1"]]
    for pi, path in enumerate(paths):
        for si, sv in enumerate(src_variants):
            node_choices = [[problem["equation1"]]]
            if sv is not None:
                node_choices.append([sv])
            for c in path[1:-1]:
                node_choices.append(
                    [EQ_TEXT[m - 1] for m in MEMBERS[c][:MAX_CANDIDATES_PER_CLASS]])
            last_members = [problem["equation2"]] + [
                EQ_TEXT[m - 1] for m in MEMBERS[path[-1]][:MAX_CANDIDATES_PER_CLASS]
                if EQ_TEXT[m - 1] != problem["equation2"]]
            node_choices.append(last_members)
            node_choices.append([problem["equation2"]])

            chain, stmts, cur = [], [], problem["equation1"]
            ok = True
            for step_idx in range(1, len(node_choices)):
                if cur in node_choices[step_idx]:
                    continue
                step_done = False
                for cand in node_choices[step_idx]:
                    t0 = time.time()
                    got = prove_step(cur, cand)
                    dt = time.time() - t0
                    if got:
                        body, route = got
                        print(f"    đường {pi}.{si} bước {step_idx}: {route} "
                              f"({dt:.0f}s)  '{cand[:44]}...'", flush=True)
                        chain.append(body)
                        stmts.append(forall_stmt(solver.parse_equation(cand)))
                        cur = cand
                        step_done = True
                        break
                    print(f"    đường {pi}.{si} bước {step_idx}: TRƯỢT ứng viên "
                          f"({dt:.0f}s) '{cand[:44]}'", flush=True)
                if not step_done:
                    ok = False
                    break
            if ok:
                code = assemble(chain, stmts)
                if solver.sanitize_lean_code(code, verdict="true") and \
                        len(code.encode()) <= solver.MAX_LEAN_CODE_BYTES:
                    return code
                print("    chuỗi ghép KHÔNG qua sanitize/size — thử tiếp")
    return None


def main(ids):
    import glob
    probs = {}
    for path in glob.glob(str(REPO / "examples/problems/*.jsonl")):
        for line in open(path, encoding="utf-8"):
            r = json.loads(line)
            probs[r["id"]] = r
    outdir = HERE / "ports" / "chains"
    outdir.mkdir(parents=True, exist_ok=True)
    for pid in ids:
        print(f"== {pid} ==")
        code = forge(probs[pid])
        if code:
            f = outdir / f"{pid}.lean"
            f.write_text(code, encoding="utf-8")
            print(f"  GHÉP XONG -> {f} ({len(code.encode()):,}B)")
        else:
            print("  không ghép được chuỗi nào")


if __name__ == "__main__":
    main(sys.argv[1:])
