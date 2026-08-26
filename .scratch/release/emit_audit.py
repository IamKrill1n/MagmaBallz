#!/usr/bin/env python3
"""ĐỐI CHỨNG PHÁT CHỨNG CHỈ — hai build, cùng bộ đề, so từng byte.

Vì sao tồn tại
--------------
Ledger `final_cert.jsonl` (2464/2469) là LEDGER GHÉP: 2284 bài đo trên build
`d968874`, 191 bài đo trên build cuối. Lý lẽ ghép, ghi trong prov, là "build
cuối phát chứng chỉ y hệt baseline cho mọi bài ngoài delta". Lý lẽ đó chỉ tồn
tại dưới dạng LỜI KHAI: không tìm thấy vật chứng thô của lượt đối chứng, và
theo mô tả thì nó chỉ phủ phía FALSE (1250 bài), bỏ trống ~1000 bài TRUE.

Script này chạy lại đối chứng đó cho ĐÚNG và GHI DẤU RA FILE.

Không gọi Lean, không gọi judge, không cần Docker — chỉ nạp hai file solver và
so `(verdict, code)`. Nên nó rẻ hơn sweep nhiều bậc.

Đọc kết quả thế nào
-------------------
  GIỐNG      hai build phát ra chứng chỉ y hệt      -> dấu baseline dùng lại được
  ĐỔI        cùng giải được, chứng chỉ khác nhau    -> PHẢI chấm lại bài đó
  MẤT        baseline có, build cuối trắng tay      -> HỒI QUY, chặn nộp
  THÊM        baseline trắng tay, build cuối có     -> bài mới, phải chấm mới tính
  TRẦN       ít nhất một build chạm trần thời gian  -> KHÔNG KẾT LUẬN ĐƯỢC

"TRẦN" được khai báo tường minh chứ không giấu: một lượt đối chứng có trần mà
im lặng về số bài chạm trần thì đọc y hệt như "đã phủ hết", trong khi không.

Cách chạy
---------
    python3 .scratch/release/emit_audit.py [--cap 25] [--out <file>]

Ghi từng dòng một và flush ngay, nên bị giết ngang vẫn giữ trọn phần đã chạy.

Song song, và vì sao nó KHÔNG phá kết quả
------------------------------------------
Chạy tuần tự mất ~3 giờ (đo: 4,7 s/bài cho cả hai build). Nhưng phép so này
KHÔNG phải phép đo thời gian — nó so chuỗi, nên tải máy không làm sai kết quả
theo cách tải máy làm sai một sweep.

Trừ đúng một chỗ, và chỗ đó có thật: vài tầng của solver cắt theo ĐỒNG HỒ
(`cp_saturation` 20 s, bao đóng, ladder, liệt kê cầu). Dưới tải, một tầng có
thể hết giờ ở lượt này mà không hết giờ ở lượt khác, và phát ra chứng chỉ
khác. Nghĩa là hai lượt của CÙNG MỘT build cũng có thể lệch nhau. Đây là bản
chất của solver, không phải của script này.

Cách xử lý: hai pha.
  Pha 1 (song song, nhanh) — quét toàn bộ, tìm ỨNG VIÊN khác biệt.
  Pha 2 (tuần tự, máy rảnh) — chạy lại RIÊNG những bài không-GIỐNG.
Bài nào ở pha 2 quay về GIỐNG thì khác biệt ở pha 1 là do tranh chấp, không
phải do build. Bài nào vẫn khác thì đó là khác biệt THẬT. Pha 2 rẻ vì tập
ứng viên nhỏ.

Kết luận cuối CHỈ đọc theo pha 2. Pha 1 một mình không kết luận gì.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import multiprocessing as mp
import signal
import subprocess
import sys
import time

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BASELINE_BUILD = "d968874"
BASELINE_LEDGER = os.path.join(
    REPO, ".scratch/release/rescue-20260825/results/final_cert.baseline432-partial-2284.jsonl")


class Hết(Exception):
    """Trần thời gian của một bài."""


def _chuông(_signum, _frame):
    raise Hết()


def nạp_solver(path: str, tên: str):
    spec = importlib.util.spec_from_file_location(tên, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def xả_cache(mod, ngưỡng: int = 0) -> None:
    """Giữ cache dưới ngưỡng để CHỐT CHẶN BỘ NHỚ CỦA SOLVER KHÔNG BAO GIỜ BẮN.

    Đây là điểm tinh tế, không phải chuyện tiết kiệm bộ nhớ. Trong lượt chấm
    thật mỗi bài là một tiến trình riêng nên cache luôn rỗng. Ở đây 2284 bài
    chạy chung một tiến trình, nên nếu để cache dồn thì `memory_exhausted()`
    của solver sẽ bắn ở bài thứ n nào đó và cắt ngắn lượt bão hòa — một khác
    biệt sinh ra bởi THỨ TỰ CHẠY chứ không phải bởi build, và nó hiện ra y hệt
    một khác biệt thật giữa hai build.

    Xả MỖI BÀI thì an toàn tuyệt đối nhưng đắt: đo được 4,6 s/bài, phần lớn là
    tính lại từ đầu. Xả THEO NGƯỠNG mua lại gần hết chi phí đó mà vẫn giữ
    nguyên tính chất cần: ngưỡng đặt dưới mức kích hoạt của chốt (50% của
    2 GB ÷ 560 byte ≈ 1,9 triệu ô) thì chốt không bao giờ có cơ hội bắn.
    """
    if ngưỡng > 0:
        đếm_ô = getattr(mod, "cache_entries", None)
        if callable(đếm_ô):
            try:
                if đếm_ô() <= ngưỡng:
                    return
            except Exception:
                pass
    xả = getattr(mod, "relieve_memory", None)
    if callable(xả):
        try:
            xả()
            return
        except Exception:
            pass
    for obj in list(vars(mod).values()):
        clear = getattr(obj, "cache_clear", None)
        if callable(clear):
            try:
                clear()
            except Exception:
                pass


def phát(mod, bài: dict, cap: float, ngưỡng: int = 0) -> tuple[str, str | None, str | None, float]:
    """Trả về (trạng thái, verdict, code, giây). Trạng thái: ok | trần | lỗi."""
    xả_cache(mod, ngưỡng)
    t = time.monotonic()
    signal.setitimer(signal.ITIMER_REAL, cap)
    try:
        out = mod.solve_problem(bài)
    except Hết:
        return "trần", None, None, time.monotonic() - t
    except Exception as exc:  # noqa: BLE001 — lỗi một bài không được giết cả lượt
        return "lỗi:" + repr(exc)[:60], None, None, time.monotonic() - t
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    dt = time.monotonic() - t
    if out is None:
        return "ok", None, None, dt
    ans = out["answer"]
    return "ok", str(ans.get("verdict")), str(ans.get("code")), dt


_W: dict = {}


def _khởi_tạo(head_path: str, base_path: str, cap: float, ngưỡng: int) -> None:
    """Mỗi tiến trình con nạp HAI build đúng một lần rồi dùng lại."""
    signal.signal(signal.SIGALRM, _chuông)
    _W["head"] = nạp_solver(head_path, "solver_head")
    _W["base"] = nạp_solver(base_path, "solver_base")
    _W["cap"] = cap
    _W["ngưỡng"] = ngưỡng


def phân_loại(st_h, c_h, v_h, st_b, c_b, v_b) -> str:
    if st_h.startswith("lỗi") or st_b.startswith("lỗi"):
        return "LỖI"
    if st_h == "trần" or st_b == "trần":
        return "TRẦN"
    if c_h is None and c_b is None:
        return "GIỐNG"          # cả hai trắng tay — giống nhau tầm thường
    if c_b is not None and c_h is None:
        return "MẤT"
    if c_b is None and c_h is not None:
        return "THÊM"
    return "GIỐNG" if (v_h, c_h) == (v_b, c_b) else "ĐỔI"


def _một_bài(việc: tuple) -> dict:
    pid, corpus, bài = việc
    cap, ng = _W["cap"], _W["ngưỡng"]
    st_h, v_h, c_h, s_h = phát(_W["head"], bài, cap, ng)
    st_b, v_b, c_b, s_b = phát(_W["base"], bài, cap, ng)
    băm = lambda c: hashlib.sha256(c.encode()).hexdigest()[:12] if c else None
    return {
        "id": pid, "corpus": corpus,
        "kết_luận": phân_loại(st_h, c_h, v_h, st_b, c_b, v_b),
        "head": {"trạng_thái": st_h, "verdict": v_h, "sha_code": băm(c_h),
                 "giây": round(s_h, 2)},
        "base": {"trạng_thái": st_b, "verdict": v_b, "sha_code": băm(c_b),
                 "giây": round(s_b, 2)},
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cap", type=float, default=25.0,
                    help="trần giây cho MỖI build MỖI bài")
    ap.add_argument("--out", default=None)
    ap.add_argument("--base", default=None,
                    help="đường dẫn solver ĐỐI CHỨNG; mặc định lấy từ git commit "
                         "BASELINE_BUILD. Dùng để so hai bản BẤT KỲ, ví dụ "
                         "trước/sau một bản vá.")
    ap.add_argument("--limit", type=int, default=0, help="chỉ chạy N bài đầu (thử)")
    ap.add_argument("--workers", type=int, default=5,
                    help="tiến trình song song cho PHA 1; pha 2 luôn tuần tự")
    ap.add_argument("--ngưỡng-cache", type=int, default=400_000,
                    dest="nguong",
                    help="chỉ xả cache khi vượt ngần này ô; 0 = xả mỗi bài")
    args = ap.parse_args()

    S = os.environ.get("SCRATCH") or os.path.join(REPO, ".scratch/release")
    out_path = args.out or os.path.join(S, "emit_audit.ledger.jsonl")

    # --- hai build ---------------------------------------------------------
    head_path = os.path.join(REPO, "EQT02-M00006.py")
    base_path = args.base or os.path.join(os.path.dirname(out_path), f"solver_{BASELINE_BUILD}.py")
    if not args.base and not os.path.exists(base_path):
        with open(base_path, "wb") as fh:
            subprocess.run(["git", "-C", REPO, "show", f"{BASELINE_BUILD}:EQT02-M00006.py"],
                           stdout=fh, check=True)

    def sha(p: str) -> str:
        return hashlib.sha256(open(p, "rb").read()).hexdigest()[:16]

    head_sha, base_sha = sha(head_path), sha(base_path)
    if head_sha == base_sha:
        print("HAI BUILD GIỐNG HỆT — không có gì để đối chứng.", file=sys.stderr)
        return 1

    # --- bộ đề: đúng những bài nằm trong baseline --------------------------
    ids: list[str] = []
    seen: set[str] = set()
    for line in open(BASELINE_LEDGER, encoding="utf-8"):
        line = line.strip()
        if not line:
            continue
        pid = str(json.loads(line)["id"])
        if pid not in seen:
            seen.add(pid)
            ids.append(pid)

    probs: dict[str, dict] = {}
    corp_of: dict[str, str] = {}
    pdir = os.path.join(REPO, "examples/problems")
    for name in sorted(os.listdir(pdir)):
        if not name.endswith(".jsonl"):
            continue
        for line in open(os.path.join(pdir, name), encoding="utf-8"):
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            probs[str(r["id"])] = r
            corp_of[str(r["id"])] = name[:-6]

    ids = [i for i in ids if i in probs]
    if args.limit:
        ids = ids[:args.limit]

    signal.signal(signal.SIGALRM, _chuông)
    việc = [(pid, corp_of.get(pid, "?"), probs[pid]) for pid in ids]

    # ---------- PHA 1: quét song song, tìm ứng viên -------------------------
    t0 = time.time()
    kết_quả: dict[str, dict] = {}
    đếm: dict[str, int] = {}
    workers = max(1, args.workers)
    print(f"PHA 1 — {len(việc)} bài, {workers} tiến trình", flush=True)
    with open(out_path, "w", encoding="utf-8") as fh:
        with mp.Pool(workers, initializer=_khởi_tạo,
                     initargs=(head_path, base_path, args.cap, args.nguong)) as pool:
            for i, r in enumerate(pool.imap_unordered(_một_bài, việc, chunksize=4), 1):
                kết_quả[r["id"]] = r
                kl = r["kết_luận"]
                đếm[kl] = đếm.get(kl, 0) + 1
                fh.write(json.dumps(r, ensure_ascii=False) + "\n")
                fh.flush()
                if kl != "GIỐNG":
                    print(f"  [pha1 {i}/{len(việc)}] {kl:6s} {r['id']}", flush=True)
                elif i % 200 == 0:
                    el = time.time() - t0
                    print(f"  [pha1 {i}/{len(việc)}] {el/60:.0f} phút, "
                          f"còn ~{el/i*(len(việc)-i)/60:.0f} phút | {đếm}", flush=True)
    giây_pha1 = time.time() - t0

    # ---------- PHA 2: xác nhận tuần tự trên máy rảnh -----------------------
    ứng_viên = [pid for pid, r in kết_quả.items() if r["kết_luận"] != "GIỐNG"]
    ứng_viên.sort()
    print(f"PHA 2 — xác nhận tuần tự {len(ứng_viên)} ứng viên", flush=True)
    t1 = time.time()
    đếm2: dict[str, int] = {}
    xác_nhận: list[dict] = []
    if ứng_viên:
        _khởi_tạo(head_path, base_path, args.cap, args.nguong)
        for pid in ứng_viên:
            r = _một_bài((pid, corp_of.get(pid, "?"), probs[pid]))
            r["pha1"] = kết_quả[pid]["kết_luận"]
            xác_nhận.append(r)
            đếm2[r["kết_luận"]] = đếm2.get(r["kết_luận"], 0) + 1
            dấu = "" if r["kết_luận"] == r["pha1"] else f"  (pha1 nói {r['pha1']})"
            print(f"  [pha2] {r['kết_luận']:6s} {pid}{dấu}", flush=True)
        with open(out_path.replace(".jsonl", ".pha2.jsonl"), "w", encoding="utf-8") as fh:
            for r in xác_nhận:
                fh.write(json.dumps(r, ensure_ascii=False) + "\n")
    giây_pha2 = time.time() - t1

    # Kết luận CHỈ đọc theo pha 2 — pha 1 chạy dưới tải nên không kết luận gì.
    khác = đếm2.get("MẤT", 0) + đếm2.get("ĐỔI", 0) + đếm2.get("THÊM", 0)
    trần = đếm2.get("TRẦN", 0) + đếm2.get("LỖI", 0)
    if khác == 0 and trần == 0:
        kết = ("ĐẠT — build cuối phát chứng chỉ Y HỆT baseline trên toàn bộ "
               f"{len(ids)} bài; dấu baseline dùng lại được nguyên vẹn")
    elif khác == 0:
        kết = (f"ĐẠT CÓ ĐIỀU KIỆN — không bài nào khác biệt, nhưng {trần} bài "
               "chạm trần/lỗi nên KHÔNG kết luận được cho riêng chúng")
    else:
        kết = (f"CÓ KHÁC BIỆT THẬT — {khác} bài (ĐỔI/MẤT/THÊM) sống sót pha 2; "
               "dấu baseline KHÔNG dùng lại nguyên vẹn được cho những bài đó")
    prov = {
        "khi": time.strftime("%Y-%m-%d %H:%M:%S"),
        "tên": "emit_audit",
        "head_build": subprocess.run(["git", "-C", REPO, "rev-parse", "--short", "HEAD"],
                                     capture_output=True, text=True).stdout.strip(),
        "head_sha": head_sha,
        "base_build": (args.base or BASELINE_BUILD),
        "base_sha": base_sha,
        "bài": len(ids),
        "trần_giây_mỗi_build": args.cap,
        "ngưỡng_xả_cache_ô": args.nguong,
        "đếm_pha1": đếm,
        "đếm_pha2": đếm2,
        "ứng_viên_pha2": [r["id"] for r in xác_nhận],
        "workers_pha1": workers,
        "giây_pha1": round(giây_pha1, 1),
        "giây_pha2": round(giây_pha2, 1),
        "ghi_chú": ("KHÔNG gọi Lean/judge/docker — chỉ so chuỗi chứng chỉ. "
                    "TRẦN nghĩa là không kết luận được bài đó, không phải giống nhau. "
                    "Kết luận đọc theo PHA 2 (tuần tự); pha 1 chỉ lọc ứng viên."),
        "kết_luận": kết,
    }
    with open(out_path + ".prov.json", "w", encoding="utf-8") as fh:
        json.dump(prov, fh, ensure_ascii=False, indent=1)
    print(json.dumps(prov, ensure_ascii=False, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
