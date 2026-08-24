# Tích hợp registry model vô hạn vào solver, THAY khối AUSTIN_1167_1763 đơn lẻ.
# Chạy SAU khi judge đã phê các template: chỉ nhúng chiều nào mọi cert mẫu
# của nó đều accepted (đọc ports/out/*.result.json).
#   python3 integrate_lane.py           -> báo cáo chiều đạt/hỏng, KHÔNG sửa
#   python3 integrate_lane.py apply     -> vá EQT02-M00006.py
import importlib.util
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).parent
REPO = HERE.parent.parent
OUT = HERE / "ports" / "out"

spec = importlib.util.spec_from_file_location("bench", HERE / "port_bench.py")
bench = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bench)
EQ, solver = bench.EQ, bench.solver

# chiều -> (mã luật nền, carrier, tên hàm op python trong solver, đảo?)
LANES = {
    "etp1659_goc":       (1659, "nat", "_etp_op_1659", False),
    "etp1659_goc2473":   (2473, "nat", "_etp_op_1659", False),
    "etp1659_dual1167":  (1167, "nat", "_etp_op_1659", True),
    "etp1659_dual2000":  (2000, "nat", "_etp_op_1659", True),
    "etp1661_goc":       (1661, "nat", "_etp_op_1661", False),
    "etp1661_dual1979":  (1979, "nat", "_etp_op_1661", True),
    "etp1701a_goc":      (1701, "nat", "_etp_op_1701a", False),
    "etp1701a_dual1839": (1839, "nat", "_etp_op_1701a", True),
    "etp1117_goc":       (1117, "int", "_etp_op_1117", False),
    "etp1117_dual2538":  (2538, "int", "_etp_op_1117", True),
    "etp1648b_goc":      (1648, "int", "_etp_op_1648b", False),
    "etp1648b_dual1924": (1924, "int", "_etp_op_1648b", True),
}

OPS_SRC = '''
def _etp_op_1659(x: int, y: int) -> int:
    if x == 0:
        return 1 if y % 2 == 0 else 0
    return x + 1 if x % 2 == y % 2 else x - 1


def _etp_op_1661(x: int, y: int) -> int:
    if x < 4:
        even = y % 2 == 0
        return ((0, 2), (1, 3), (2, 0), (4, 1))[x][0 if even else 1]
    return x - 1 if x % 2 == y % 2 else x + 1


def _etp_op_1701a(x: int, y: int) -> int:
    if y == 0:
        return 0
    return y - 1 if x % 2 == y % 2 else y + 1


def _etp_op_1117(a: int, b: int) -> int:
    return 2 * a - b // 2


def _etp_op_1648b(x: int, y: int) -> int:
    return x + 1 if x > y else x - 1
'''


def lane_status():
    manifest = json.load(open(OUT / "manifest.json"))
    per = {}
    for m in manifest:
        res = OUT / (m["file"] + ".result.json")
        st = None
        if res.exists():
            st = json.load(open(res))["status"]
        per.setdefault(m["model"], []).append(st)
    ok_lanes = []
    for lane, sts in sorted(per.items()):
        acc = sum(s == "accepted" for s in sts)
        rej = sum(s not in (None, "accepted") for s in sts)
        pend = sum(s is None for s in sts)
        verdict = "ĐẠT" if rej == 0 and acc > 0 else ("CHỜ" if rej == 0 else "HỎNG")
        print(f"{lane:20s} accepted={acc:3d} hỏng={rej} chưa chấm={pend} -> {verdict}")
        if verdict == "ĐẠT":
            ok_lanes.append(lane)
    return ok_lanes


def canon_literal(eq_id):
    eq = EQ[eq_id]
    m = {}

    def w(t):
        if t[0] == "var":
            if t[1] not in m:
                m[t[1]] = f"v{len(m)}"
            return ("var", m[t[1]])
        return ("op", w(t[1]), w(t[2]))

    return repr((w(eq["lhs"]), w(eq["rhs"])))


def apply(ok_lanes):
    S = REPO / "EQT02-M00006.py"
    src = S.read_text(encoding="utf-8")

    entries = []
    for lane in ok_lanes:
        base, carrier, opname, dual = LANES[lane]
        tpl = (HERE / "ports" / (lane + ".lean")).read_text(encoding="utf-8")
        entries.append(
            f'    {{\n'
            f'        "name": "{lane}",\n'
            f'        "base_canon": {canon_literal(base)},\n'
            f'        "carrier": "{carrier}",\n'
            f'        "op": {opname},\n'
            f'        "dual": {dual},\n'
            f'        "template": {tpl!r},\n'
            f'    }},'
        )
    registry = (
        OPS_SRC
        + "\n\n# Registry model vô hạn port từ ETP ManuallyProved — mỗi chiều đã được\n"
        + "# judge phê trên mẫu cert trước khi nhúng. Khớp theo hình dạng alpha-\n"
        + "# canonical của GIẢ THUYẾT; điểm vi phạm của đích tìm bằng quét cửa sổ\n"
        + "# xác định (không ngẫu nhiên). Emit chỉ khi tìm được vi phạm.\n"
        + "INFINITE_MODEL_LANE = (\n" + "\n".join(entries) + "\n)\n\n"
        + '''_ETP_NAT_WINDOW = tuple(range(14))
_ETP_INT_WINDOW = tuple(range(-10, 11))


def _etp_render_value(v: int, carrier: str) -> str:
    if carrier == "int":
        return f"({v} : Int)" if v >= 0 else f"(({v}) : Int)"
    return str(v)


def named_infinite_certificate(
    eq1: dict[str, Any], eq2: dict[str, Any]
) -> tuple[str, str] | None:
    """Model vô hạn ETP: khớp giả thuyết theo hình dạng, phát cert với điểm
    vi phạm tìm động. Bao trùm cả cặp CHƯA TỪNG THẤY có cùng giả thuyết."""
    key = alpha_canonical_pair(eq1)
    for lane in INFINITE_MODEL_LANE:
        if key != lane["base_canon"]:
            continue
        base_op = lane["op"]
        op = (lambda a, b, _o=base_op: _o(b, a)) if lane["dual"] else base_op
        window = _ETP_INT_WINDOW if lane["carrier"] == "int" else _ETP_NAT_WINDOW
        variables = eq2["variables"]
        assignment = None
        total = len(window) ** len(variables)
        for index in range(total):
            rest, vals = index, []
            for _ in variables:
                rest, digit = divmod(rest, len(window))
                vals.append(window[digit])
            env = dict(zip(variables, vals))
            env["op"] = op
            try:
                if eval_term(eq2["lhs"], env) != eval_term(eq2["rhs"], env):
                    assignment = [env[v] for v in variables]
                    break
            except Exception:
                break
        if assignment is None:
            continue
        args = " ".join(_etp_render_value(v, lane["carrier"]) for v in assignment)
        code = lane["template"].replace("{VIOLATION}", args)
        if not sanitize_lean_code(code, verdict="false"):
            continue
        return f'false:witness_inf:{lane["name"]}', code
    return None
'''
    )

    if "# Austin-pair infinite countermodel" in src:
        # lần đầu: thay khối AUSTIN đơn lẻ, giữ lại alpha_canonical_pair
        start = src.index("# Austin-pair infinite countermodel")
        end_marker = 'return "false:witness_inf:austin_1167_1763", AUSTIN_1167_1763_CERT\n    return None\n'
        end = src.index(end_marker) + len(end_marker)
        seg = src[start:end]
        keep_start = seg.index("def alpha_canonical_pair")
        keep_end = seg.index("def named_infinite_certificate")
        kept = seg[keep_start:keep_end]
        src = src[:start] + kept + registry + src[end:]
    else:
        # tái áp: thay khối đã sinh (từ _etp_op_1659 tới trước hàm kế tiếp)
        start = src.index("def _etp_op_1659")
        end = src.index("def singleton_true_certificate")
        src = src[:start] + registry.lstrip("\n") + "\n\n" + src[end:]
    S.write_text(src, encoding="utf-8")
    print(f"đã vá solver: {len(ok_lanes)} chiều, cỡ file {S.stat().st_size:,}B")


if __name__ == "__main__":
    ok = lane_status()
    if len(sys.argv) > 1 and sys.argv[1] == "apply":
        apply(ok)
