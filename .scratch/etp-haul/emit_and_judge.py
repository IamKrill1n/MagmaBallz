# Phát chứng chỉ vô hạn từ template port + chấm judge theo lô.
#   python3 emit_and_judge.py emit           -> sinh ports/out/<tpl>__<h>_<t>.lean
#   python3 emit_and_judge.py judge [N]      -> chấm (tối đa N cert, mặc định hết)
# Nguồn cặp: danh sách Austin (giả thuyết == luật nền của chiều) ∪ cặp trực
# tiếp từ ManuallyProved. Mỗi cặp được KIỂM SỐ HỌC lúc phát: model thỏa E1
# trên cửa sổ + tìm được điểm vi phạm E2. Judge là phán quyết cuối.
import importlib.util
import itertools
import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).parent
REPO = HERE.parent.parent
OUT = HERE / "ports" / "out"

spec = importlib.util.spec_from_file_location("bench", HERE / "port_bench.py")
bench = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bench)
EQ = bench.EQ


def render_nat(v):
    return str(v)


def render_int(v):
    return f"({v} : Int)" if v >= 0 else f"(({v}) : Int)"


def swap(op):
    return lambda a, b: op(b, a)


op1659 = bench.op_1659
op1701 = bench.op_1701_8
op1117 = bench.make_op_1117(bench.div_f)
op1648 = bench.op_1648b

# tên template -> (op theo CHIỀU của template, miền, mã luật nền E1, render)
REG = {
    "etp1659_goc":      (op1659,       bench.NAT, 1659, render_nat),
    "etp1659_goc2473":  (op1659,       bench.NAT, 2473, render_nat),
    "etp1659_dual1167": (swap(op1659), bench.NAT, 1167, render_nat),
    "etp1659_dual2000": (swap(op1659), bench.NAT, 2000, render_nat),
    "etp1701a_goc":     (op1701,       bench.NAT, 1701, render_nat),
    "etp1701a_dual1839": (swap(op1701), bench.NAT, 1839, render_nat),
    "etp1117_goc":      (op1117,       bench.INT, 1117, render_int),
    "etp1117_dual2538": (swap(op1117), bench.INT, 2538, render_int),
    "etp1648b_goc":     (op1648,       bench.INT, 1648, render_int),
    "etp1648b_dual1924": (swap(op1648), bench.INT, 1924, render_int),
}


def austin_pairs():
    out = set()
    for line in open(HERE / "Austin_implications.txt", encoding="utf-8"):
        nums = re.findall(r"\d+", line)
        if len(nums) >= 2:
            out.add((int(nums[0]), int(nums[1])))
    return out


def direct_pairs():
    d = json.load(open(HERE / "manually_proved" / "direct_pairs.json"))
    return {(h, t) for v in d.values() for h, t in v}


def find_violation(eq, op, domain):
    vs = eq["variables"]
    for vals in itertools.product(domain, repeat=len(vs)):
        env = dict(zip(vs, vals))
        if not bench.holds_at(eq, env, op):
            return [env[v] for v in vs]
    return None


def emit():
    OUT.mkdir(parents=True, exist_ok=True)
    pool = austin_pairs() | direct_pairs()
    manifest, skipped = [], []
    for name, (op, dom, base, rend) in REG.items():
        template = (HERE / "ports" / (name + ".lean")).read_text(encoding="utf-8")
        sat, _ = bench.check_eq(EQ[base], op, dom)
        assert sat, f"{name}: op KHÔNG thỏa luật nền {base} — chiều sai"
        for h, t in sorted(pool):
            if h != base:
                continue
            vio = find_violation(EQ[t], op, dom)
            if vio is None:
                skipped.append((name, h, t))
                continue
            args = " ".join(rend(v) for v in vio)
            code = template.replace("{VIOLATION}", args)
            out = OUT / f"{name}__{h}_{t}.lean"
            out.write_text(code, encoding="utf-8")
            manifest.append({"file": out.name, "model": name, "eq1": h, "eq2": t})
    json.dump(manifest, open(OUT / "manifest.json", "w"), indent=1)
    print(f"đã phát {len(manifest)} cert, bỏ qua {len(skipped)} cặp (không tìm được vi phạm trên cửa sổ)")
    for s in skipped[:10]:
        print("  bỏ:", s)


def judge():
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 10**9
    sys.path.insert(0, str(REPO))
    sys.path.insert(0, str(REPO / ".scratch/release"))
    import judge_lock
    from pipeline.proxy import DEFAULT_PROOF_POLICY

    eq_lines = [l.strip() for l in open(HERE / "equations.txt", encoding="utf-8")]
    manifest = json.load(open(OUT / "manifest.json"))
    good = bad = done = 0
    for m in manifest:
        res_path = OUT / (m["file"] + ".result.json")
        if res_path.exists():
            r = json.load(open(res_path))
            good += r["status"] == "accepted"
            bad += r["status"] != "accepted"
            continue
        if done >= limit:
            continue
        done += 1
        problem = {
            "id": f'{m["model"]}_{m["eq1"]}_{m["eq2"]}',
            "equation1": eq_lines[m["eq1"] - 1],
            "equation2": eq_lines[m["eq2"] - 1],
            "proof_policy": DEFAULT_PROOF_POLICY,
        }
        code = (OUT / m["file"]).read_text(encoding="utf-8")
        r = judge_lock.judged(problem, "false", code)
        json.dump(r, open(res_path, "w"), indent=1)
        ok = r.get("status") == "accepted"
        good += ok
        bad += not ok
        print(f'{"OK " if ok else "FAIL"} {m["file"]}: {r.get("status")} '
              f'{(r.get("message") or "")[:110]}', flush=True)
    print(f"KẾT QUẢ: accepted {good}, hỏng {bad}, còn lại "
          f"{len(manifest) - good - bad}")


if __name__ == "__main__":
    {"emit": emit, "judge": judge}[sys.argv[1]]()
