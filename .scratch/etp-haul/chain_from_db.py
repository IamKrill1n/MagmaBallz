# GHÉP CHUỖI THUẦN TRA CỨU: đường cạnh-explicit + thân từ kho (không engine).
#   python3 chain_from_db.py hard3_0314 "2923,2628,...,1623"
import importlib.util
import json
import pathlib
import re
import subprocess
import sys

HERE = pathlib.Path(__file__).parent
REPO = HERE.parent.parent
spec = importlib.util.spec_from_file_location("solver", REPO / "EQT02-M00006.py")
solver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(solver)

EQ_TEXT = [l.strip() for l in open(HERE / "equations.txt", encoding="utf-8")]
DB = json.load(open(HERE / "edge_proofs_full.json"))


def forall_stmt(eq):
    vs = " ".join(eq["variables"])
    lhs = solver.term_to_lean(eq["lhs"])
    rhs = solver.term_to_lean(eq["rhs"])
    return f"∀ {vs} : G, {lhs} = {rhs}"


def edge_body(a, b):
    """(dòng thân đã indent 4, cần_mathlib) — thân chứng minh a=>b, giả thuyết tên h."""
    rec = DB[f"{a}>{b}"]
    fam, src = rec["fam"], rec["src"]
    if fam == "VampireProven":
        out = subprocess.run(
            [sys.executable, str(HERE / "vampire_translate.py"), str(a), str(b)],
            capture_output=True, text=True)
        assert out.returncode == 0, f"dịch Vampire {a}>{b} hỏng:\n{out.stderr[-600:]}"
        lines = out.stdout.splitlines()
        i = lines.index("  intro G _ h")
        return ["  " + l if l.strip() else l for l in lines[i + 1:] if l.strip()], False
    if ":= by" in src.split("\n", 1)[0] or "\n  " in src:
        # tactic-style (TrivialBruteforce/NthRewrites, EquationSearch...)
        body = src.split(":=", 1)[1]
        assert body.lstrip().startswith("by"), f"{a}>{b}: khuôn lạ"
        tac = body.lstrip()[2:]
        lines = [l for l in tac.splitlines() if l.strip()]
        need_mathlib = "nth_rewrite" in src
        return ["  " + l if l.strip() else l for l in lines], need_mathlib
    # term-style (SimpleRewrites): ':= λ ... => ...' / ':= fun ... => ...'
    term = src.split(":=", 1)[1].strip()
    return [f"    exact ({term})"], False


def build(problem, id_path):
    texts = [EQ_TEXT[i - 1] for i in id_path]
    assert texts[0] == problem["equation1"] and texts[-1] == problem["equation2"]
    lines = []
    need_mathlib = False
    for k in range(1, len(id_path)):
        a, b = id_path[k - 1], id_path[k]
        body, nm = edge_body(a, b)
        need_mathlib = need_mathlib or nm
        stmt = forall_stmt(solver.parse_equation(texts[k]))
        lines.append(f"  have h{k} : {stmt} := by")
        lines.append(f"    have h := h{k - 1}")
        lines.extend(body)
        print(f"  cạnh {k}/{len(id_path)-1} {a}=>{b} [{DB[f'{a}>{b}']['fam']}] ✓",
              flush=True)
    header = ["import JudgeProblem"]
    if need_mathlib:
        header.append("import Mathlib.Tactic.NthRewrite")
    code = "\n".join(header) + "\n\ndef submission : Goal := by\n  intro G _ h0\n" \
        + "\n".join(lines) + f"\n  exact h{len(id_path)-1}\n"
    return code


if __name__ == "__main__":
    import glob
    probs = {}
    for p in glob.glob(str(REPO / "examples/problems/*.jsonl")):
        for l in open(p, encoding="utf-8"):
            r = json.loads(l)
            probs[r["id"]] = r
    pid = sys.argv[1]
    idp = [int(x) for x in sys.argv[2].split(",")]
    code = build(probs[pid], idp)
    out = HERE / "ports" / "chains" / f"{pid}_lookup.lean"
    out.write_text(code, encoding="utf-8")
    print(f"GHÉP XONG -> {out} ({len(code.encode()):,}B)")
