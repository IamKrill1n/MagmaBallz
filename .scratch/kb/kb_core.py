"""LÕI HOÀN TẤT KNUTH-BENDIX KHÔNG THẤT BẠI (unfailing completion).

Lớp bài: đơn-đẳng-thức (một giả thuyết E1, một đích E2, magma một phép toán).
Đây đúng lớp mà Waldmeister/Twee thống trị, và là lớp mà cp_saturation hiện
tại xử lý bằng dò-khe-hở hai chiều — không định hướng, không liên-rút-gọn,
nên pool phình tới sát trần bộ nhớ.

Ba mảnh solver CHƯA có, viết ở đây:
  1. mgu()      — hợp nhất tổng quát nhất (solver chỉ có khớp MỘT chiều)
  2. kbo_gt()   — thứ tự rút gọn Knuth-Bendix, để ĐỊNH HƯỚNG đẳng thức
  3. completion — vòng hoàn tất với liên-rút-gọn (tập luật CO lại, không phình)

Hạng tử dùng đúng biểu diễn của solver: ("var", tên) / ("op", trái, phải).
Mọi luật ghi vết cha để dựng chứng minh Lean ở bước sau (kb_proof.py).
"""
from __future__ import annotations

import heapq
import itertools
import time
from typing import Any

Term = tuple

# ---------------------------------------------------------------- hạng tử


def is_var(t: Term) -> bool:
    return t[0] == "var"


def term_size(t: Term) -> int:
    if is_var(t):
        return 1
    return 1 + term_size(t[1]) + term_size(t[2])


def term_vars(t: Term) -> set[str]:
    if is_var(t):
        return {t[1]}
    return term_vars(t[1]) | term_vars(t[2])


def var_count(t: Term, v: str) -> int:
    if is_var(t):
        return 1 if t[1] == v else 0
    return var_count(t[1], v) + var_count(t[2], v)


def subst(t: Term, s: dict[str, Term]) -> Term:
    if is_var(t):
        return s.get(t[1], t)
    return ("op", subst(t[1], s), subst(t[2], s))


def positions(t: Term):
    """Mọi vị trí (đường dẫn) trong hạng tử, gốc trước."""
    yield ()
    if not is_var(t):
        for i in (1, 2):
            for p in positions(t[i]):
                yield (i,) + p


def at(t: Term, p: tuple) -> Term:
    for i in p:
        t = t[i]
    return t


def put(t: Term, p: tuple, new: Term) -> Term:
    if not p:
        return new
    i = p[0]
    parts = list(t)
    parts[i] = put(t[i], p[1:], new)
    return tuple(parts)


def rename(t: Term, tag: str) -> Term:
    """Đổi tên biến để hai luật không đụng biến nhau khi hợp nhất."""
    if is_var(t):
        return ("var", tag + t[1])
    return ("op", rename(t[1], tag), rename(t[2], tag))


# ------------------------------------------------------- 1. HỢP NHẤT (MGU)


def _occurs(v: str, t: Term) -> bool:
    if is_var(t):
        return t[1] == v
    return _occurs(v, t[1]) or _occurs(v, t[2])


def mgu(a: Term, b: Term) -> dict[str, Term] | None:
    """Hợp nhất tổng quát nhất của hai hạng tử, hoặc None nếu không hợp nhất
    được. Khác match_term của solver: cả HAI phía đều có thể gán biến."""
    s: dict[str, Term] = {}
    stack = [(a, b)]
    while stack:
        x, y = stack.pop()
        x = subst(x, s) if is_var(x) and x[1] in s else x
        y = subst(y, s) if is_var(y) and y[1] in s else y
        if x == y:
            continue
        if is_var(x):
            if _occurs(x[1], y):
                return None
            s = {k: subst(v, {x[1]: y}) for k, v in s.items()}
            s[x[1]] = y
            continue
        if is_var(y):
            if _occurs(y[1], x):
                return None
            s = {k: subst(v, {y[1]: x}) for k, v in s.items()}
            s[y[1]] = x
            continue
        stack.append((x[1], y[1]))
        stack.append((x[2], y[2]))
    return s


def match_one_way(pattern: Term, target: Term,
                  s: dict[str, Term] | None = None) -> dict[str, Term] | None:
    """Khớp một chiều: chỉ biến của `pattern` được gán."""
    if s is None:
        s = {}
    stack = [(pattern, target)]
    while stack:
        p, t = stack.pop()
        if is_var(p):
            if p[1] in s:
                if s[p[1]] != t:
                    return None
            else:
                s[p[1]] = t
            continue
        if is_var(t) or t[0] != "op":
            return None
        stack.append((p[1], t[1]))
        stack.append((p[2], t[2]))
    return s


# ------------------------------------------------------ 2. THỨ TỰ KBO


def kbo_gt(s: Term, t: Term) -> bool:
    """s > t theo Knuth-Bendix: trọng số mọi ký hiệu = 1, một phép toán duy
    nhất nên không cần thứ tự ưu tiên ký hiệu. Điều kiện biến bắt buộc: mọi
    biến xuất hiện trong t không được nhiều hơn trong s (nếu không, viết lại
    có thể nhân bản biến vô hạn)."""
    for v in term_vars(t):
        if var_count(t, v) > var_count(s, v):
            return False
    ws, wt = term_size(s), term_size(t)
    if ws != wt:
        return ws > wt
    # cùng trọng số: so sánh từ điển trên cấu trúc (trái trước, phải sau)
    if is_var(s) or is_var(t):
        return False
    if s[1] != t[1]:
        return kbo_gt(s[1], t[1])
    return kbo_gt(s[2], t[2])


def orient(l: Term, r: Term) -> tuple[Term, Term] | None:
    """Định hướng đẳng thức thành luật viết lại theo chiều GIẢM."""
    if kbo_gt(l, r):
        return (l, r)
    if kbo_gt(r, l):
        return (r, l)
    return None


# ------------------------------------------------- 3. VIẾT LẠI + HOÀN TẤT


class Rule:
    __slots__ = ("lhs", "rhs", "src", "idx")

    def __init__(self, lhs: Term, rhs: Term, src: Any, idx: int):
        self.lhs, self.rhs = lhs, rhs
        self.src = src        # vết dựng lại chứng minh
        self.idx = idx

    def weight(self) -> int:
        return term_size(self.lhs) + term_size(self.rhs)

    def __repr__(self) -> str:
        return f"R{self.idx}"


def rewrite_step(t: Term, rules: list[Rule]) -> tuple[Term, Rule, tuple, dict] | None:
    """Một bước viết lại trong-ngoài (innermost-leftmost đủ dùng)."""
    for p in positions(t):
        sub = at(t, p)
        if is_var(sub):
            continue
        for rule in rules:
            m = match_one_way(rule.lhs, sub)
            if m is not None:
                return put(t, p, subst(rule.rhs, m)), rule, p, m
    return None


def normalize(t: Term, rules: list[Rule], max_steps: int = 400,
              trace: list | None = None) -> Term:
    """Đưa hạng tử về dạng chuẩn theo tập luật."""
    for _ in range(max_steps):
        step = rewrite_step(t, rules)
        if step is None:
            return t
        t, rule, p, m = step
        if trace is not None:
            trace.append((rule, p, m))
    return t


def critical_pairs(r1: Rule, r2: Rule):
    """Cặp tới hạn: siêu vị r1 vào mọi vị trí không-biến của vế trái r2."""
    l1 = rename(r1.lhs, "a_")
    rr1 = rename(r1.rhs, "a_")
    l2 = rename(r2.lhs, "b_")
    rr2 = rename(r2.rhs, "b_")
    for p in positions(l2):
        sub = at(l2, p)
        if is_var(sub):
            continue
        u = mgu(l1, sub)
        if u is None:
            continue
        left = subst(put(l2, p, rr1), u)
        right = subst(rr2, u)
        if left != right:
            yield left, right, p, u


def collapse_witness(l: Term, r: Term) -> tuple[Term, Term] | None:
    """Đẳng thức ép magma SỤP ĐỔ (mọi phần tử bằng nhau).

    Nếu một vế là BIẾN TRẦN không xuất hiện ở vế kia — ví dụ `t = z` với
    z ∉ vars(t) — thì cố định các biến khác và cho z chạy: t không đổi trong
    khi z nhận mọi giá trị, nên mọi phần tử bằng nhau. Đây đúng bổ đề E2 mà
    reja23 dựng cho order5_0016 (`v0 ◇ v1 = v2`), và từ nó MỌI đích đều đúng.
    """
    for a, b in ((l, r), (r, l)):
        if is_var(a) and a[1] not in term_vars(b):
            return (a, b)
    return None


def ordered_rewrite_step(t: Term, rules: list["Rule"],
                         eqs: list["Rule"]) -> tuple[Term, Any, tuple, dict] | None:
    """Một bước: luật định hướng dùng trực tiếp; đẳng thức KHÔNG định hướng
    được chỉ dùng khi THỂ HIỆN cụ thể là giảm (viết lại có thứ tự) — đây là
    phần 'không thất bại' của unfailing completion."""
    for p in positions(t):
        sub = at(t, p)
        if is_var(sub):
            continue
        for rule in rules:
            m = match_one_way(rule.lhs, sub)
            if m is not None:
                return put(t, p, subst(rule.rhs, m)), rule, p, m
        for eq in eqs:
            for src, dst in ((eq.lhs, eq.rhs), (eq.rhs, eq.lhs)):
                m = match_one_way(src, sub)
                if m is None:
                    continue
                si, di = subst(src, m), subst(dst, m)
                if kbo_gt(si, di):
                    return put(t, p, di), eq, p, m
    return None


def onormalize(t: Term, rules: list["Rule"], eqs: list["Rule"],
               max_steps: int = 300, trace: list | None = None) -> Term:
    for _ in range(max_steps):
        step = ordered_rewrite_step(t, rules, eqs)
        if step is None:
            return t
        t, rule, p, m = step
        if trace is not None:
            trace.append((rule, p, m))
    return t


def complete(hyp_l: Term, hyp_r: Term, goal_l: Term, goal_r: Term, *,
             deadline: float, max_rules: int = 3000,
             max_pairs: int = 500000) -> dict[str, Any]:
    """Hoàn tất KHÔNG THẤT BẠI: giữ cả luật định hướng (R) lẫn đẳng thức không
    định hướng được (E), siêu vị giữa mọi cặp, viết lại có thứ tự, và phát
    hiện SỤP ĐỔ — thứ mà bản chỉ-định-hướng vứt mất.

    Chọn theo trọng số (best-first, kiểu Waldmeister)."""
    counter = itertools.count()
    rules: list[Rule] = []
    eqs: list[Rule] = []
    pending: list[tuple[int, int, Term, Term, Any]] = []

    def push(l: Term, r: Term, src: Any):
        heapq.heappush(pending,
                       (term_size(l) + term_size(r), next(counter), l, r, src))

    push(hyp_l, hyp_r, ("hyp",))
    stats = {"pairs": 0, "rules": 0, "eqs": 0, "dropped": 0}

    def goal_joined() -> bool:
        return onormalize(goal_l, rules, eqs) == onormalize(goal_r, rules, eqs)

    while pending:
        if time.monotonic() >= deadline:
            return {"proved": False, "how": None, "rules": rules, "eqs": eqs,
                    "stats": stats, "stop": "time"}
        if stats["pairs"] > max_pairs:
            return {"proved": False, "how": None, "rules": rules, "eqs": eqs,
                    "stats": stats, "stop": "pairs"}
        _w, _c, l, r, src = heapq.heappop(pending)
        stats["pairs"] += 1
        l = onormalize(l, rules, eqs)
        r = onormalize(r, rules, eqs)
        if l == r:
            stats["dropped"] += 1
            continue

        cw = collapse_witness(l, r)
        if cw is not None:
            return {"proved": True, "how": "collapse", "rules": rules,
                    "eqs": eqs + [Rule(l, r, src, -1)], "stats": stats,
                    "stop": "collapse"}

        o = orient(l, r)
        if o is None:
            item = Rule(l, r, src, -(len(eqs) + 1))
            eqs.append(item)
            stats["eqs"] = len(eqs)
        else:
            nl, nr = o
            item = Rule(nl, nr, src, len(rules))
            keep = []
            for old in rules:
                red = any(match_one_way(nl, at(old.lhs, p)) is not None
                          for p in positions(old.lhs)
                          if not is_var(at(old.lhs, p)))
                if red:
                    push(old.lhs, old.rhs, old.src)
                else:
                    keep.append(old)
            rules = keep
            rules.append(item)
            stats["rules"] = len(rules)

        if goal_joined():
            return {"proved": True, "how": "joined", "rules": rules,
                    "eqs": eqs, "stats": stats, "stop": "proved"}
        if len(rules) + len(eqs) > max_rules:
            return {"proved": False, "how": None, "rules": rules, "eqs": eqs,
                    "stats": stats, "stop": "max_rules"}

        for other in rules + eqs:
            for a, b, p, u in critical_pairs(item, other):
                push(a, b, ("cp", item.idx, other.idx, p))
            if other is not item:
                for a, b, p, u in critical_pairs(other, item):
                    push(a, b, ("cp", other.idx, item.idx, p))
    return {"proved": False, "how": None, "rules": rules, "eqs": eqs,
            "stats": stats, "stop": "saturated"}
