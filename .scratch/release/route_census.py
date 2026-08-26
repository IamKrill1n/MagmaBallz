#!/usr/bin/env python3
"""ĐIỀU TRA DÂN SỐ ROUTE — route nào ăn bài nào, và tốn bao nhiêu.

Bản gốc nằm trong scratchpad `/private/tmp/.../5aa77320.../scratchpad` và đã bị
dọn mất cùng phiên đó; đây là bản viết lại. Dây chuyền `run_chain.sh` chặng 6
gọi `$S/route_census.py` — đường dẫn đó nay trỏ vào hư không, nên chặng 6 sẽ
không bao giờ xong nếu không trỏ lại vào file này.

Câu hỏi nó trả lời
------------------
1. Mỗi route ăn bao nhiêu bài, ở corpus nào? (dân số)
2. Route đó tốn bao nhiêu giây, tính cả những bài nó KHÔNG ăn? (giá)
3. Route nào hiếm tới mức đáng ngờ là đã bị tầng khác thâu tóm? (ứng viên cắt)

Điều nó KHÔNG trả lời, và đừng đọc nhầm
---------------------------------------
Nó KHÔNG chứng minh route nào bị thâu tóm. `solve_problem` dừng ở route ĐẦU
TIÊN ăn được, nên census chỉ thấy NGƯỜI THẮNG, không thấy ai khác cũng ăn được
bài đó. Muốn biết cắt một route có mất bài không thì phải chạy ablation: tắt
đúng route đó rồi quét lại. Census chỉ thu hẹp danh sách phải ablation từ ~20
route xuống vài route hiếm — đó là toàn bộ công dụng của nó.

Cắt một tầng dựa trên census đơn thuần là đúng loại sai lầm mà sổ vận hành
gọi là "thay thế": đã một lần lấy 3 bài và mất 3 bài.

Cách chạy
---------
    python3 .scratch/release/route_census.py [--workers 5] [--cap 60]
"""
from __future__ import annotations

import argparse
import collections
import importlib.util
import json
import multiprocessing as mp
import os
import signal
import time

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


class Hết(Exception):
    pass


def _chuông(_s, _f):
    raise Hết()


_W: dict = {}


def _khởi_tạo(path: str, cap: float) -> None:
    signal.signal(signal.SIGALRM, _chuông)
    spec = importlib.util.spec_from_file_location("solver_census", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    _W["m"] = mod
    _W["cap"] = cap


def _một_bài(việc: tuple) -> dict:
    pid, corpus, bài = việc
    mod, cap = _W["m"], _W["cap"]
    xả = getattr(mod, "relieve_memory", None)
    if callable(xả):
        try:
            xả()
        except Exception:
            pass
    t = time.monotonic()
    signal.setitimer(signal.ITIMER_REAL, cap)
    route, verdict, lỗi = None, None, None
    try:
        out = mod.solve_problem(bài)
        if out is not None:
            route = str(out["route"])
            verdict = str(out["answer"].get("verdict"))
    except Hết:
        route = "(TRẦN)"
    except Exception as exc:  # noqa: BLE001
        route = "(LỖI)"
        lỗi = repr(exc)[:120]
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    return {"id": pid, "corpus": corpus, "route": route or "(KHÔNG GIẢI ĐƯỢC)",
            "verdict": verdict, "giây": round(time.monotonic() - t, 3),
            "lỗi": lỗi}


def họ_route(route: str) -> str:
    """Gom về TẦNG, không phải biến thể. `true:cp_saturation:rel_beam:29` ->
    `true:cp_saturation`."""
    phần = route.split(":")
    return ":".join(phần[:2]) if len(phần) >= 2 else route


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--workers", type=int, default=5)
    ap.add_argument("--cap", type=float, default=60.0,
                    help="trần giây mỗi bài; bài chạm trần được đếm riêng")
    ap.add_argument("--out", default=os.path.join(REPO, ".scratch/release/route_census.jsonl"))
    args = ap.parse_args()

    pdir = os.path.join(REPO, "examples/problems")
    việc = []
    for name in sorted(os.listdir(pdir)):
        if not name.endswith(".jsonl"):
            continue
        for line in open(os.path.join(pdir, name), encoding="utf-8"):
            line = line.strip()
            if line:
                r = json.loads(line)
                việc.append((str(r["id"]), name[:-6], r))

    print(f"census {len(việc)} bài, {args.workers} tiến trình, trần {args.cap}s",
          flush=True)
    t0 = time.time()
    rows = []
    solver = os.path.join(REPO, "EQT02-M00006.py")
    with open(args.out, "w", encoding="utf-8") as fh:
        with mp.Pool(args.workers, initializer=_khởi_tạo,
                     initargs=(solver, args.cap)) as pool:
            for i, r in enumerate(pool.imap_unordered(_một_bài, việc, chunksize=4), 1):
                rows.append(r)
                fh.write(json.dumps(r, ensure_ascii=False) + "\n")
                fh.flush()
                if i % 250 == 0:
                    el = time.time() - t0
                    print(f"  [{i}/{len(việc)}] {el/60:.0f} phút, "
                          f"còn ~{el/i*(len(việc)-i)/60:.0f} phút", flush=True)

    dân_số = collections.Counter(họ_route(r["route"]) for r in rows)
    giá = collections.defaultdict(float)
    for r in rows:
        giá[họ_route(r["route"])] += r["giây"]
    theo_corpus: dict[str, collections.Counter] = collections.defaultdict(collections.Counter)
    for r in rows:
        theo_corpus[họ_route(r["route"])][r["corpus"]] += 1

    tổng_giây = sum(r["giây"] for r in rows)
    print("\n%-34s %6s %9s %9s" % ("TẦNG", "BÀI", "GIÂY", "GIÂY/BÀI"))
    for tầng, n in dân_số.most_common():
        print("%-34s %6d %9.1f %9.2f" % (tầng, n, giá[tầng], giá[tầng] / n))
    print(f"\ntổng {len(rows)} bài, {tổng_giây/60:.1f} phút công (không tính song song)")

    hiếm = [t for t, n in dân_số.items()
            if n <= 3 and t not in ("(KHÔNG GIẢI ĐƯỢC)", "(TRẦN)", "(LỖI)")]
    print(f"\nỨNG VIÊN PHẢI ABLATION (≤3 bài, có thể đã bị thâu tóm): {len(hiếm)}")
    for t in sorted(hiếm):
        ids = [r["id"] for r in rows if họ_route(r["route"]) == t]
        print(f"   {t:34s} {ids}")
    print("\nĐây là DANH SÁCH PHẢI KIỂM, không phải danh sách được cắt. "
          "Cắt mà không ablation là 'thay thế' — đã một lần +3/-3 bài.")

    prov = {
        "khi": time.strftime("%Y-%m-%d %H:%M:%S"),
        "tên": "route_census",
        "bài": len(rows),
        "trần_giây": args.cap,
        "workers": args.workers,
        "giây": round(time.time() - t0, 1),
        "dân_số": dict(dân_số),
        "giây_theo_tầng": {k: round(v, 1) for k, v in giá.items()},
        "theo_corpus": {k: dict(v) for k, v in theo_corpus.items()},
        "ứng_viên_ablation": sorted(hiếm),
        "ghi_chú": ("Chỉ thấy route THẮNG, không thấy route nào khác cũng ăn "
                    "được bài đó. Không kết luận thâu tóm từ file này."),
    }
    with open(args.out + ".prov.json", "w", encoding="utf-8") as fh:
        json.dump(prov, fh, ensure_ascii=False, indent=1)
    print("\nROUTE CENSUS DONE")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
