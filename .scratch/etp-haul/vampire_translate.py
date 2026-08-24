# BỘ DỊCH VAMPIRE -> Lean policy-sạch.
#
# Bản ghi VampireProven có dạng: dây `have eqK (vars) : LHS = RHS :=
# superpose eqA eqB` (mỗi bước MỘT cú chồng-lấp, phát biểu ĐÍCH cho sẵn),
# kết bằng `subsumption`. Bộ dịch bỏ khung phản chứng/skolem, chỉ:
#   1. tái dựng từng phương trình dương bằng tìm-lại một bước viết lại
#      (cha làm luật, hai chiều, mọi vị trí) — đích đã biết nên đây là
#      REPLAY xác định, không phải tìm kiếm mở;
#   2. đóng goal bằng phép thế của phương trình cuối (khớp một chiều).
# Phát ra term Eq.trans/congrArg — đúng khuôn cert solver, qua policy judge.
#
#   python3 vampire_translate.py 1021 47       # dịch thử một cạnh
import importlib.util
import json
import pathlib
import re
import sys
from itertools import product

HERE = pathlib.Path(__file__).parent
REPO = HERE.parent.parent
spec = importlib.util.spec_from_file_location("solver", REPO / "EQT02-M00006.py")
solver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(solver)

EQ_TEXT = [l.strip() for l in open(HERE / "equations.txt", encoding="utf-8")]
DB = json.load(open(HERE / "edge_proofs_full.json"))

LETTERS = "abcdefghijkl"
VARS = list(LETTERS)


def _xsub(txt):
    import re as _re
    return _re.sub(r"\bX(\d+)\b", lambda m: LETTERS[int(m.group(1))], txt)


def parse_side(txt):
    """'(X0 ◇ (X1 ◇ X2))' -> Term, X{i} đổi thành chữ cái đơn."""
    return solver.parse_term(_xsub(txt).strip(), VARS)


def all_paths(term):
    yield ()
    if term[0] == "op":
        for i in (1, 2):
            for p in all_paths(term[i]):
                yield (i,) + p


def subterm(term, path):
    for i in path:
        term = term[i]
    return term


def replace(term, path, new):
    if not path:
        return new
    i = path[0]
    parts = list(term)
    parts[i] = replace(term[i], path[1:], new)
    return tuple(parts)


def rewrite_once(cur, rules, pool):
    """Mọi kết quả sau MỘT bước viết lại cur bằng một luật (2 chiều, mọi vị trí).
    Biến tự do phía đích (chiều đảo của luật) được gán từ `pool` (hạng tử con
    của đích cuối) — vẫn là replay đóng vì đích đã biết. Trả
    (kết_quả, (rule_idx, dir, path, subst))."""
    out = []
    for ri, (lhs, rhs) in enumerate(rules):
        for direction, (src, dst) in enumerate(((lhs, rhs), (rhs, lhs))):
            dst_vars = solver.term_vars(dst)
            for path in all_paths(cur):
                sub = {}
                if not solver.match_term(src, subterm(cur, path), sub):
                    continue
                missing = sorted(dst_vars - set(sub))
                if not missing:
                    new = replace(cur, path, solver.instantiate_term(dst, sub))
                    out.append((new, (ri, direction, path, dict(sub))))
                    continue
                if len(missing) > 2:
                    continue
                combos = [{}]
                for v in missing:
                    combos = [dict(c, **{v: cand}) for c in combos for cand in pool]
                    if len(combos) > 400:
                        combos = combos[:400]
                for extra in combos:
                    s2 = dict(sub, **extra)
                    new = replace(cur, path, solver.instantiate_term(dst, s2))
                    out.append((new, (ri, direction, path, s2)))
    return out


def find_derivation(target_l, target_r, rules, max_steps=3):
    """BFS <=max_steps bước viết lại từ target_l tới target_r. Trả dãy bước."""
    pool = list({st for st in solver.term_subterms(target_r)} |
                {st for st in solver.term_subterms(target_l)})
    frontier = [(target_l, [])]
    seen = {target_l}
    for _ in range(max_steps):
        nxt = []
        for cur, trail in frontier:
            for new, step in rewrite_once(cur, rules, pool):
                if new == target_r:
                    return trail + [step]
                if new not in seen and solver.term_size(new) <= 60:
                    seen.add(new)
                    nxt.append((new, trail + [step]))
        frontier = nxt
    return None


def context_lambda(term, path):
    """(fun t => <term với lỗ ở path>)."""
    marker = ("var", "__HOLE__")
    holed = replace(term, path, marker)
    txt = solver.term_to_lean(holed).replace("__HOLE__", "t")
    return f"(fun t => {txt})"


def emit_step_proof(cur, steps, rules_names, rules):
    """Chuỗi Eq.trans của các bước viết lại cur -> ... Trả biểu thức Lean."""
    parts = []
    for ri, direction, path, sub in steps:
        lhs, rhs = rules[ri]
        src = lhs if direction == 0 else rhs
        rule_vars = sorted(solver.term_vars(lhs) | solver.term_vars(rhs))
        args = " ".join(
            solver.term_to_lean(sub.get(v, ("var", v))) for v in rule_vars)
        base = f"({rules_names[ri]} {args})"
        if direction == 1:
            base = f"{base}.symm"
        if path:
            base = f"(congrArg {context_lambda(cur, path)} {base})"
        parts.append(base)
        # tiến cur theo bước này
        dst = rhs if direction == 0 else lhs
        cur = replace(cur, path, solver.instantiate_term(dst, sub))
    expr = parts[0]
    for p in parts[1:]:
        expr = f"(Eq.trans {expr} {p})"
    return expr


def translate(a, b):
    src = DB[f"{a}>{b}"]["src"]
    hyp_eq = solver.parse_equation(EQ_TEXT[a - 1])
    goal_eq = solver.parse_equation(EQ_TEXT[b - 1])

    # 1) gom các have DƯƠNG: 'have eqN (vars) : L = R := ...'
    have_pat = re.compile(
        r"have (eq\d+)(?: \(([^)]*): G\))? : (.+?) := (superpose (eq\d+) (eq\d+)|mod_symm \(h \.\.\))",
        re.M)
    pos_eqs = {}      # tên -> (lhs Term, rhs Term)
    order = []
    hyp_name = None
    for m in have_pat.finditer(src):
        name, _vs, stmt, how = m.group(1), m.group(2), m.group(3), m.group(4)
        if "≠" in stmt:
            continue  # nhánh skolem âm — bỏ, không cần cho bản dựng dương
        l_txt, r_txt = stmt.rsplit(" = ", 1)
        l, r = parse_side(l_txt), parse_side(r_txt)
        pos_eqs[name] = (l, r)
        m2 = re.match(r"superpose (eq\d+) (eq\d+)", how)
        parents = (m2.group(1), m2.group(2)) if m2 else None
        order.append((name, how, parents))
        if how.startswith("mod_symm"):
            hyp_name = name

    # 2) dựng thân từng have
    lines = []
    names = []
    rules = []
    def rules_snapshot():
        return list(rules), list(names)

    for name, how, parents in order:
        l, r = pos_eqs[name]
        vs = sorted(solver.term_vars(l) | solver.term_vars(r))
        binder = f"({' '.join(vs)} : G) " if vs else ""
        stmt = f"{solver.term_to_lean(l)} = {solver.term_to_lean(r)}"
        if how.startswith("mod_symm"):
            # hướng của hypothesis: goal dạng 'x = RHS' -> mod_symm là symm
            hl, hr = hyp_eq["lhs"], hyp_eq["rhs"]
            # thử khớp (l,r) với (hr,hl) qua đổi tên biến
            sub = {}
            if solver.match_term(hr, l, sub) and solver.match_term(hl, r, dict(sub)):
                hyp_vars = hyp_eq["variables"]
                sub2 = {}
                solver.match_term(hr, l, sub2)
                solver.match_term(hl, r, sub2)
                args = " ".join(
                    solver.term_to_lean(sub2.get(v, ("var", v))) for v in hyp_vars)
                lines.append(f"  have {name} {binder}: {stmt} := (h {args}).symm")
            else:
                sub2 = {}
                assert solver.match_term(hl, l, sub2) and \
                    solver.match_term(hr, r, sub2), f"{name}: hyp không khớp"
                args = " ".join(
                    solver.term_to_lean(sub2.get(v, ("var", v)))
                    for v in hyp_eq["variables"])
                lines.append(f"  have {name} {binder}: {stmt} := h {args}")
        else:
            if parents:
                sel = [i for i, n in enumerate(names) if n in parents]
                rs = [rules[i] for i in sel]
                ns = [names[i] for i in sel]
            else:
                rs, ns = rules_snapshot()
            steps = find_derivation(l, r, rs)
            flipped = False
            if steps is None:
                steps = find_derivation(r, l, rs)
                flipped = True
            assert steps is not None, f"{name}: không tái dựng được"
            start = r if flipped else l
            expr = emit_step_proof(start, steps, ns, rs)
            if flipped:
                expr = f"({expr}).symm"
            lines.append(f"  have {name} {binder}: {stmt} := {expr}")
        rules.append(pos_eqs[name])
        names.append(name)

    # 3) đóng goal: tìm eq dương + phép thế khớp goal (cả hai hướng)
    gl, gr = goal_eq["lhs"], goal_eq["rhs"]
    close = None
    for name in reversed(names):
        l, r = pos_eqs[name]
        for flip in (False, True):
            a_, b_ = (l, r) if not flip else (r, l)
            sub = {}
            if solver.match_term(a_, gl, sub) and solver.match_term(b_, gr, sub):
                vs = sorted(solver.term_vars(l) | solver.term_vars(r))
                args = " ".join(
                    solver.term_to_lean(sub.get(v, ("var", v))) for v in vs)
                close = f"({name} {args})" + (".symm" if flip else "")
                break
        if close:
            break
    assert close, "không đóng được goal từ eq dương nào"

    gvars = " ".join(goal_eq["variables"])
    body = "\n".join(lines)
    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        f"  intro {gvars}\n"
        f"{body}\n"
        f"  exact {close}\n"
    )


if __name__ == "__main__":
    a, b = int(sys.argv[1]), int(sys.argv[2])
    code = translate(a, b)
    print(code)
