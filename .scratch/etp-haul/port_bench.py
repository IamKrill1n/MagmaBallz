# Bàn kiểm số học cho các model vô hạn port từ ETP ManuallyProved.
# Mỗi model: mô phỏng op bằng Python, kiểm trên cửa sổ hữu hạn:
#   - thỏa luật nền + mọi luật giả thuyết của các cặp tuyên bố
#   - tìm điểm vi phạm cho từng đích tuyên bố
# Đây là bằng chứng số học TRƯỚC khi viết Lean; Lean + judge là phán quyết cuối.
import importlib.util
import itertools
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).parent
REPO = HERE.parent.parent
spec = importlib.util.spec_from_file_location("solver", REPO / "EQT02-M00006.py")
solver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(solver)

EQ = {}  # id -> eq dict đã parse
for i, line in enumerate(open(HERE / "equations.txt", encoding="utf-8"), start=1):
    EQ[i] = solver.parse_equation(line.strip())


def eval_term(term, env, op):
    if term[0] == "var":
        return env[term[1]]
    return op(eval_term(term[1], env, op), eval_term(term[2], env, op))


def holds_at(eq, env, op):
    return eval_term(eq["lhs"], env, op) == eval_term(eq["rhs"], env, op)


def check_eq(eq, op, domain):
    """(thỏa_trên_toàn_cửa_sổ, điểm_vi_phạm_đầu_tiên_hoặc_None)"""
    vs = eq["variables"]
    for vals in itertools.product(domain, repeat=len(vs)):
        if not holds_at(eq, dict(zip(vs, vals)), op):
            return False, dict(zip(vs, vals))
    return True, None


# ---------------- các op mô phỏng (nguyên văn ETP, chưa đảo đối số) --------
def op_1659(x, y):
    if x == 0:
        return 1 if y % 2 == 0 else 0
    return x + 1 if x % 2 == y % 2 else x - 1


def op_1661(x, y):
    if x == 0:
        return 0 if y % 2 == 0 else 2
    if x == 1:
        return 1 if y % 2 == 0 else 3
    if x == 2:
        return 2 if y % 2 == 0 else 0
    if x == 3:
        return 4 if y % 2 == 0 else 1
    n = x - 4
    return n + 3 if x % 2 == y % 2 else n + 5


def op_1701_8(x, y):
    if y == 0:
        return 0
    n = y - 1
    return n if x % 2 == y % 2 else n + 2


def op_1701_3253(x, y):
    if y == 1:
        return 1 if x in (0, 1) else 0
    if y == 0:
        return 0
    n = y - 2
    return n + 1 if x % 2 == y % 2 else n + 3


def op_1701_4587(x, y):
    table = {(0, 2): 3, (0, 3): 2, (1, 0): 2, (1, 1): 0, (2, 3): 4, (3, 2): 3}
    if (x, y) in table:
        return table[(x, y)]
    if y == 0:
        return 1
    if y == 1:
        return 0
    if y == 2:
        return 0
    return y - 1 if x % 2 == y % 2 else y + 1


def _sign(v):
    return 0 if v == 0 else (-1 if v < 0 else 1)


def make_op_1117(div):
    return lambda a, b: 2 * a - div(b, 2)


def div_t(a, b):  # cắt về 0
    q = abs(a) // b
    return -q if a < 0 else q


def div_f(a, b):  # floor
    return a // b


def op_1648(x, y):
    return x - _sign(y - x)


def op_1648b(x, y):
    return x + 1 if x > y else x - 1


def op_1437(a, b):
    (a1, a2), (b1, b2) = a, b
    first = (b1 if a1 == 0 else a1 - 1) if a2 == (b2 + 2) % 3 else a1 + 1
    return (first, (b2 + 1) % 3)


def op_3342(a, b):
    if a is None or b is None:
        return None
    (x, y), (c, d) = a, b
    if y == d and (x == c or x + 1 == c):
        return (0, y + 1)
    if y + 1 == d and x >= c:
        return (x - c + 1, y)
    if y == d + 1 and x < c:
        return (c - x, d)
    return None


NAT = list(range(14))
INT = list(range(-10, 11))
NF3 = [(n, f) for n in range(8) for f in range(3)]
OPT = [None] + [(a, b) for a in range(6) for b in range(6)]

direct = json.load(open(HERE / "manually_proved" / "direct_pairs.json"))

MODELS = [
    ("1659", op_1659, NAT, direct["Equation1659"]),
    ("1661", op_1661, NAT, direct["Equation1661"]),
    ("1701_8", op_1701_8, NAT, None),
    ("1701_3253", op_1701_3253, NAT, None),
    ("1701_4587", op_1701_4587, NAT, None),
    ("1117_t", make_op_1117(div_t), INT, direct["Equation1117"]),
    ("1117_f", make_op_1117(div_f), INT, direct["Equation1117"]),
    ("1648", op_1648, INT, direct["Equation1648"]),
    ("1648b", op_1648b, INT, direct["Equation1648"]),
    ("1437", op_1437, NF3, direct["Equation1437"]),
    ("3342", op_3342, OPT, direct["Equation3342"]),
]
# 1701 có 3 model chung một file — chia cặp theo model bằng luật nền:
# op nào thỏa giả thuyết nào thì nhận cặp đó.
P1701 = direct["Equation1701"]

results = {}
for name, op, dom, pairs in MODELS:
    if pairs is None:
        pairs = P1701
    ok_pairs, fail = [], []
    dual_op = lambda a, b, _o=op: _o(b, a)
    for h, t in pairs:
        got = None
        for tag, o in (("goc", op), ("dual", dual_op)):
            sat, _ = check_eq(EQ[h], o, dom)
            if not sat:
                continue
            viol, pt = check_eq(EQ[t], o, dom)
            if not viol:
                got = (h, t, tag, pt)
                break
        if got:
            ok_pairs.append(got)
        else:
            fail.append((h, t, "không chiều nào nhận"))
    results[name] = ok_pairs
    print(f"model {name:10s}: nhận {len(ok_pairs):2d} cặp, hỏng {len(fail)}")
    for f in fail:
        print("   !!", f)

total = {(h, t) for v in results.values() for (h, t, *_r) in v}
print(f"\nTổng cặp trực tiếp kiểm số học ĐẠT: {len(total)}")
json.dump({k: v for k, v in results.items()},
          open(HERE / "port_validation.json", "w"), default=str)
