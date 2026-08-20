"""Đặc trưng quan hệ cho bộ xếp hạng ứng viên bổ đề.

Mọi đặc trưng tính được từ (ứng viên, src, dst, giả thuyết, pool) bằng số
nguyên/thực rẻ tiền — không cần numpy, chạy được trong sandbox. Bộ này dùng
chung cho: huấn luyện offline, chưng cất GBDT, và suy luận trong solver.
"""
from __future__ import annotations


def subterms(t, acc=None):
    if acc is None: acc = set()
    acc.add(t)
    if t[0] == "op":
        subterms(t[1], acc); subterms(t[2], acc)
    return acc


def tvars(t, acc=None):
    if acc is None: acc = set()
    if t[0] == "var": acc.add(t[1])
    else: tvars(t[1], acc); tvars(t[2], acc)
    return acc


def size(t):
    return 1 if t[0] == "var" else 1 + size(t[1]) + size(t[2])


def depth(t):
    return 0 if t[0] == "var" else 1 + max(depth(t[1]), depth(t[2]))


def matches_any(m6, side, targets):
    for tgt in targets:
        s = {}
        if m6.match_term(side, tgt, s):
            return 1
    return 0


FEATURE_NAMES = [
    "size_l", "size_r", "size_sum", "size_diff", "depth_l", "depth_r",
    "nvars_l", "nvars_r", "nvars_shared", "nvars_goal_shared",
    "sub_overlap_l", "sub_overlap_r", "sub_overlap_total", "sub_overlap_frac",
    "match_goal_l", "match_goal_r",
    "gap_relevance", "size_vs_h", "size_vs_goal",
    "n_cites", "deriv_depth", "is_var_l", "is_var_r",
    "hmodel_survives",
]


def extract(m6, cand, src, dst, eq1, deriv_depth=0, hmodel_ok=1):
    """Trả list số theo đúng thứ tự FEATURE_NAMES."""
    l, r = cand["lhs"], cand["rhs"]
    sl, sr = subterms(l), subterms(r)
    goal_subs = subterms(src) | subterms(dst)
    vl, vr = tvars(l), tvars(r)
    goal_vars = tvars(src) | tvars(dst)
    h_size = size(eq1["lhs"]) + size(eq1["rhs"])
    g_size = size(src) + size(dst)
    ov_l = len(sl & goal_subs); ov_r = len(sr & goal_subs)
    tot = len(sl | sr)
    return [
        size(l), size(r), size(l) + size(r), abs(size(l) - size(r)),
        depth(l), depth(r),
        len(vl), len(vr), len(vl & vr), len((vl | vr) & goal_vars),
        ov_l, ov_r, ov_l + ov_r, (ov_l + ov_r) / max(tot, 1),
        matches_any(m6, l, goal_subs), matches_any(m6, r, goal_subs),
        m6._gap_relevance(cand, tuple(goal_subs)),
        (size(l) + size(r)) / max(h_size, 1),
        (size(l) + size(r)) / max(g_size, 1),
        len(cand.get("cites", ())), deriv_depth,
        1 if l[0] == "var" else 0, 1 if r[0] == "var" else 0,
        hmodel_ok,
    ]
