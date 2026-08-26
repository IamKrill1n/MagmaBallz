#!/usr/bin/env python3
"""TÍNH LẠI ĐIỂM — dựng lại ledger có vật chứng cho từng dòng.

Vì sao
------
`final_cert.jsonl` khai 2464/2469, nhưng 2278 dòng trong đó mang dấu judge đo
trên build `d968874`, không phải build đem nộp. Lý lẽ tái dùng dấu là "hai
build phát chứng chỉ y hệt" — `emit_audit.py` vừa cho thấy điều đó KHÔNG đúng
với mọi bài: có những bài phát ra chứng chỉ khác (đáp án vẫn thế, file chứng
minh khác). Dấu judge chấm cho file cũ; file mới CHƯA AI CHẤM.

Nguyên tắc số 3 của sổ vận hành: không tính điểm cho bài nào chưa có dấu judge.

Ba bước
-------
  rescan  bước 2 — vét nhóm TRẦN với trần rộng hơn, tuần tự, KHÔNG tốn judge.
                   Phần lớn TRẦN là do build CŨ chậm (đo được: 81/81 bài base
                   chạm trần, head chỉ 5) nên nới trần là giải quyết được.
  judge   bước 3 — chấm lại ĐÚNG những bài không chứng minh được là giống nhau.
                   Chạy thật: hộp cát docker, không LLM, tuần tự.
  ledger  bước 4 — ghép: (GIỐNG → dấu cũ) + (delta → dấu build cuối) +
                   (chấm lại → dấu mới). Mỗi dòng ghi rõ nguồn dấu của nó.

    python3 .scratch/release/recount.py rescan [--cap 120]
    python3 .scratch/release/recount.py judge  [--timeout 600]
    python3 .scratch/release/recount.py ledger
"""
from __future__ import annotations

import argparse
import collections
import importlib.util
import json
import os
import signal
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent
REL = REPO / ".scratch/release"
RESCUE = REL / "rescue-20260825"

AUDIT = REL / "emit_audit.ledger.jsonl"
AUDIT_P2 = REL / "emit_audit.ledger.pha2.jsonl"
RESCAN = REL / "recount_rescan.jsonl"
JUDGED = REL / "recount_judged.jsonl"
FINAL = REL / "recount_final_cert.jsonl"
CŨ = RESCUE / "results/final_cert.jsonl"

# Thư mục nộp phải chứa ĐÚNG MỘT file solver.py — `pipeline/proxy.py:575` và
# `pipeline/marathon_runner.py:104` từ chối thẳng nếu có bất kỳ entry nào khác,
# và từ chối ở mức "chưa chạy solver", tức 0 điểm mà mã thoát vẫn 0.
# `.scratch/release/submission/` có kèm SUBMISSION_NOTE.md + BUILD_COMMIT.txt
# nên KHÔNG dùng trực tiếp được; dựng một thư mục sạch chỉ có solver.py.
SUBMISSION = REL / "subs_recount" / "m6final"


def _dựng_thư_mục_nộp_sạch() -> None:
    import shutil
    SUBMISSION.mkdir(parents=True, exist_ok=True)
    for e in SUBMISSION.iterdir():
        if e.name != "solver.py":
            (shutil.rmtree if e.is_dir() else os.remove)(e)
    shutil.copyfile(REPO / "EQT02-M00006.py", SUBMISSION / "solver.py")
    thừa = [e.name for e in SUBMISSION.iterdir() if e.name != "solver.py"]
    assert not thừa, f"thư mục nộp còn file thừa: {thừa}"
CHƯA_KẾT_LUẬN = {"ĐỔI", "TRẦN", "LỖI", "MẤT", "THÊM"}


# ---------------------------------------------------------------- dùng chung
def đọc_jsonl(p: Path) -> list[dict]:
    if not p.exists():
        return []
    return [json.loads(l) for l in p.read_text(encoding="utf-8").splitlines() if l.strip()]


def kết_luận_đối_chứng() -> dict[str, str]:
    """id -> kết luận CUỐI CÙNG, ưu tiên nguồn xác nhận muộn nhất.

    Thứ tự đè: pha 1 < pha 2 (tuần tự) < rescan (trần rộng). Mỗi lớp sau chạy
    trong điều kiện tốt hơn lớp trước, nên nó có quyền lật kết luận."""
    kl: dict[str, str] = {}
    for p in (AUDIT, AUDIT_P2, RESCAN):
        for r in đọc_jsonl(p):
            kl[r["id"]] = r["kết_luận"]
    return kl


def nạp_đề() -> tuple[dict[str, dict], dict[str, str]]:
    probs, corp = {}, {}
    pdir = REPO / "examples/problems"
    for f in sorted(pdir.glob("*.jsonl")):
        for line in f.read_text(encoding="utf-8").splitlines():
            if line.strip():
                r = json.loads(line)
                probs[str(r["id"])] = r
                corp[str(r["id"])] = f.stem
    return probs, corp


# ------------------------------------------------------------- BƯỚC 2: rescan
def bước_rescan(cap: float) -> int:
    ea_spec = importlib.util.spec_from_file_location("emit_audit", REL / "emit_audit.py")
    ea = importlib.util.module_from_spec(ea_spec)
    ea_spec.loader.exec_module(ea)

    kl = kết_luận_đối_chứng()
    cần = sorted(pid for pid, v in kl.items() if v in CHƯA_KẾT_LUẬN)
    if not cần:
        print("không còn bài nào chưa kết luận — bỏ qua rescan")
        return 0
    probs, corp = nạp_đề()
    cần = [p for p in cần if p in probs]
    print(f"BƯỚC 2 — vét lại {len(cần)} bài ở trần {cap}s, tuần tự", flush=True)

    signal.signal(signal.SIGALRM, ea._chuông)
    base_path = REL / f"solver_{ea.BASELINE_BUILD}.py"
    ea._khởi_tạo(str(REPO / "EQT02-M00006.py"), str(base_path), cap, 400_000)

    đếm: collections.Counter = collections.Counter()
    t0 = time.time()
    băm = lambda c: __import__("hashlib").sha256(c.encode()).hexdigest()[:12] if c else None
    with RESCAN.open("w", encoding="utf-8") as fh:
        for i, pid in enumerate(cần, 1):
            bài = probs[pid]
            # Trần KHÔNG đối xứng, và đây là chỗ tiết kiệm phần lớn thời gian.
            # Đo ở pha 1: trong 81 bài chạm trần, bản CŨ chạm 81 lần, bản mới
            # chỉ 5 — bản cũ mới là bản lê lết (nó thiếu oracle nên đốt trọn
            # ngân sách tìm phản mẫu trên những bài chắc chắn TRUE).
            # Cấp cho bản mới trần đầy đủ, rồi cấp cho bản cũ một trần TỈ LỆ
            # theo thời gian bản mới vừa tiêu. Bản cũ chậm ~2x, nên 4x là dư
            # rộng; bài nào vượt 4x thì bản cũ khác hẳn về đường đi, và cách
            # rẻ hơn để kết luận là chấm lại ở bước 3 chứ không phải chờ nó.
            st_h, v_h, c_h, s_h = ea.phát(ea._W["head"], bài, cap, 400_000)
            trần_base = max(30.0, min(180.0, 4.0 * s_h)) if st_h != "trần" else cap
            st_b, v_b, c_b, s_b = ea.phát(ea._W["base"], bài, trần_base, 400_000)
            r = {
                "id": pid, "corpus": corp.get(pid, "?"),
                "kết_luận": ea.phân_loại(st_h, c_h, v_h, st_b, c_b, v_b),
                "head": {"trạng_thái": st_h, "verdict": v_h, "sha_code": băm(c_h),
                         "giây": round(s_h, 2)},
                "base": {"trạng_thái": st_b, "verdict": v_b, "sha_code": băm(c_b),
                         "giây": round(s_b, 2), "trần": round(trần_base, 1)},
            }
            r["trước_đó"] = kl[pid]
            đếm[r["kết_luận"]] += 1
            fh.write(json.dumps(r, ensure_ascii=False) + "\n")
            fh.flush()
            dấu = "" if r["kết_luận"] == r["trước_đó"] else f"  (trước: {r['trước_đó']})"
            print(f"  [{i}/{len(cần)}] {r['kết_luận']:6s} {pid}{dấu}", flush=True)
    print(f"\nBƯỚC 2 XONG sau {(time.time()-t0)/60:.0f} phút: {dict(đếm)}")
    còn = sum(v for k, v in đếm.items() if k in CHƯA_KẾT_LUẬN)
    print(f"còn {còn} bài phải chấm lại ở bước 3")
    return 0


# -------------------------------------------------------------- BƯỚC 3: judge
#
# HAI ĐƯỜNG, và việc chọn đúng đường là chỗ tiết kiệm phần lớn thời gian.
#
# Câu hỏi mở với 171 bài này KHÔNG phải "build cuối có giải nổi trong ngân
# sách không" — baseline đã trả lời rồi, chúng đều đã được giải. Câu hỏi mở là
# "chứng chỉ MỚI mà build cuối phát ra có biên dịch qua judge không".
#
#   ĐƯỜNG CERT (156 bài) — build cuối đã phát ra chứng chỉ trong lượt đối
#     chứng (trung vị 3,5 s). Sinh lại tại chỗ rồi đưa THẲNG cho judge. Trả
#     lời đúng câu hỏi mở, và bỏ được cả lượt chạy container 600 s.
#     Giả định phải khai: đường này KHÔNG kiểm lại trần bộ nhớ hộp cát và
#     ngân sách thời gian. Hợp lệ ở đây vì baseline đã kiểm hai thứ đó cho
#     đúng những bài này, và cái thay đổi giữa hai build là NỘI DUNG chứng
#     chỉ chứ không phải khả năng giải.
#
#   ĐƯỜNG ĐẦY ĐỦ (15 bài) — build cuối chạm trần 25 s ở lượt đối chứng, nên
#     ta CHƯA biết nó phát ra gì. Phải chạy trọn pipeline trong hộp cát.


def _đường_cert(pids, probs, corp, kl, fh, lean_timeout: int) -> int:
    import importlib.util as iu
    sys.path.insert(0, str(REPO))
    sys.path.insert(0, str(REL))
    from pipeline.proxy import DEFAULT_PROOF_POLICY  # noqa: E402
    from judge_lock import judged  # noqa: E402

    # Hạn Lean 300 s — đúng con số đường Solo hứa với thí sinh
    # (pipeline/config.json). Mặc định của lời gọi judge trực tiếp là 120 s,
    # tức KHẮT KHE HƠN giải thật: một chứng chỉ cần 200 s sẽ bị báo trượt oan.
    os.environ["LEAN_TIMEOUT_SECONDS"] = str(lean_timeout)

    spec = iu.spec_from_file_location("solver_head", REPO / "EQT02-M00006.py")
    m = iu.module_from_spec(spec)
    spec.loader.exec_module(m)

    ok = 0
    for i, pid in enumerate(pids, 1):
        t = time.time()
        bài = probs[pid]
        try:
            m.relieve_memory()
        except Exception:
            pass
        out = m.solve_problem(bài)
        if out is None:
            row = {"solver": "m6final", "id": pid, "corpus": corp.get(pid, "?"),
                   "expected": bài.get("answer"), "solved": False, "verdict": None,
                   "judge_statuses": [], "judge_calls": 0, "llm_calls": 0,
                   "elapsed": round(time.time() - t, 1),
                   "nguồn": "chấm-lại:cert", "ghi_chú": "build cuối không phát ra gì"}
        else:
            ans = out["answer"]
            jp = {"id": bài["id"], "eq1_id": bài.get("eq1_id"), "eq2_id": bài.get("eq2_id"),
                  "equation1": bài["equation1"], "equation2": bài["equation2"],
                  "proof_policy": bài.get("proof_policy") or DEFAULT_PROOF_POLICY}
            r = judged(jp, str(ans["verdict"]), str(ans["code"]), yield_to_sweep=False)
            st = str(r.get("status"))
            row = {"solver": "m6final", "id": pid, "corpus": corp.get(pid, "?"),
                   "expected": bài.get("answer"), "solved": st == "accepted",
                   "verdict": ans["verdict"], "judge_statuses": [st], "judge_calls": 1,
                   "llm_calls": 0, "route": out.get("route"),
                   "error_code": r.get("error_code"),
                   "elapsed": round(time.time() - t, 1), "nguồn": "chấm-lại:cert"}
        ok += bool(row["solved"])
        fh.write(json.dumps(row, ensure_ascii=False) + "\n")
        fh.flush()
        print(f"  [cert {i}/{len(pids)}] {'OK' if row['solved'] else '--'} {pid:26s} "
              f"{str(row['verdict']):5s} {row['elapsed']:>6}s "
              f"{','.join(row['judge_statuses'])[:32]}", flush=True)
    return ok


def _đường_đầy_đủ(pids, probs, corp, fh, timeout: int) -> int:
    _dựng_thư_mục_nộp_sạch()
    sys.path.insert(0, str(REPO))
    from pipeline.proxy import load_config, run_solver  # noqa: E402
    config = load_config(None)
    config["solver"]["timeout_seconds"] = timeout
    config["sandbox"]["mode"] = os.environ.get("SB_SANDBOX_MODE", "docker")
    ok = 0
    for i, pid in enumerate(pids, 1):
        t = time.time()
        os.environ["JUDGE_ARTIFACT_DIR"] = str(REL / "artifacts_recount" / f"{pid}.{int(t)}")
        try:
            res = run_solver(SUBMISSION, probs[pid], config)
        except Exception as exc:  # noqa: BLE001
            res = {"solved": False, "verdict": None, "llm_calls": 0, "judge_calls": 0,
                   "log": [{"type": "error", "message": repr(exc)}]}
        statuses = [str((e.get("response") or {}).get("status")
                        or (e.get("response") or {}).get("error_code") or "?")
                    for e in res.get("log", []) if e.get("type") == "judge"]
        # Lỗi hạ tầng PHẢI đi vào dòng kết quả. Lượt trước 15 bài trả về
        # 0,0 giây / judge_calls=0 / mã thoát 0 và nhìn y hệt "giải không ra";
        # thông báo thật ("submission must contain only solver.py") nằm trong
        # log và bị vứt đi.
        lỗi = [str(e.get("message"))[:200] for e in res.get("log", [])
               if e.get("type") == "error"]
        row = {"solver": "m6final", "id": pid, "corpus": corp.get(pid, "?"),
               "lỗi": lỗi or None,
               "expected": probs[pid].get("answer"), "solved": bool(res.get("solved")),
               "verdict": res.get("verdict"), "judge_statuses": statuses,
               "llm_calls": res.get("llm_calls", 0), "judge_calls": res.get("judge_calls", 0),
               "elapsed": round(time.time() - t, 1), "nguồn": "chấm-lại:đầy-đủ"}
        ok += bool(row["solved"])
        fh.write(json.dumps(row, ensure_ascii=False) + "\n")
        fh.flush()
        print(f"  [đủ {i}/{len(pids)}] {'OK' if row['solved'] else '--'} {pid:26s} "
              f"{str(row['verdict']):5s} {row['elapsed']:>6}s "
              f"{','.join(statuses)[:32]}", flush=True)
    return ok


def bước_judge(timeout: int, giới_hạn: int, đường: str, lean_timeout: int) -> int:
    for key in ("OPENAI_API_KEY", "OPENROUTER_API_KEY"):
        os.environ.pop(key, None)   # con số đem nộp không được phụ thuộc khóa API

    kl = kết_luận_đối_chứng()
    audit = {r["id"]: r for r in đọc_jsonl(AUDIT)}
    for p in (AUDIT_P2, RESCAN):
        for r in đọc_jsonl(p):
            audit[r["id"]] = r
    probs, corp = nạp_đề()
    cần = [pid for pid, v in kl.items() if v in CHƯA_KẾT_LUẬN and pid in probs]

    có_cert, phải_chạy = [], []
    for pid in sorted(cần):
        h = audit.get(pid, {}).get("head", {})
        (có_cert if h.get("trạng_thái") == "ok" and h.get("sha_code") else phải_chạy).append(pid)
    if giới_hạn:
        có_cert, phải_chạy = có_cert[:giới_hạn], phải_chạy[:giới_hạn]

    đã = {r["id"] for r in đọc_jsonl(JUDGED)}
    có_cert = [p for p in có_cert if p not in đã]
    phải_chạy = [p for p in phải_chạy if p not in đã]
    print(f"BƯỚC 3 — {len(có_cert)} bài đường CERT (Lean {lean_timeout}s), "
          f"{len(phải_chạy)} bài đường ĐẦY ĐỦ ({timeout}s, docker) | không LLM",
          flush=True)

    t0 = time.time()
    ok = 0
    with JUDGED.open("a", encoding="utf-8") as fh:
        if đường in ("auto", "cert") and có_cert:
            ok += _đường_cert(có_cert, probs, corp, kl, fh, lean_timeout)
        if đường in ("auto", "full") and phải_chạy:
            ok += _đường_đầy_đủ(phải_chạy, probs, corp, fh, timeout)
    print(f"\nBƯỚC 3 XONG sau {(time.time()-t0)/60:.0f} phút: {ok} accepted")
    return 0


# ------------------------------------------------------------- BƯỚC 4: ledger
def bước_ledger() -> int:
    cũ = {r["id"]: r for r in đọc_jsonl(CŨ)}
    mới = {r["id"]: r for r in đọc_jsonl(JUDGED)}
    kl = kết_luận_đối_chứng()

    ra: list[dict] = []
    nguồn: collections.Counter = collections.Counter()
    treo: list[str] = []
    for pid, r in cũ.items():
        r = dict(r)
        corpus = str(r.get("corpus", ""))
        if corpus.startswith("delta_night"):
            r["nguồn_dấu"] = "delta (build cuối)"       # vốn đã đo trên build cuối
        elif pid in mới:
            r = dict(mới[pid])
            r["nguồn_dấu"] = "chấm lại (build cuối)"
        elif kl.get(pid) == "GIỐNG":
            r["nguồn_dấu"] = "baseline, đối chứng GIỐNG"
        elif pid in kl:
            r["nguồn_dấu"] = f"TREO — đối chứng {kl[pid]}, chưa chấm lại"
            treo.append(pid)
        else:
            r["nguồn_dấu"] = "TREO — chưa đối chứng"
            treo.append(pid)
        nguồn[r["nguồn_dấu"].split(" —")[0]] += 1
        ra.append(r)

    with FINAL.open("w", encoding="utf-8") as fh:
        for r in ra:
            fh.write(json.dumps(r, ensure_ascii=False) + "\n")

    # Điểm CHẮC = chỉ những dòng có dấu judge thuộc về build đem nộp,
    # hoặc dòng baseline đã chứng minh được là phát ra chứng chỉ y hệt.
    chắc = sum(1 for r in ra if r.get("solved") and not r["nguồn_dấu"].startswith("TREO"))
    treo_giải = sum(1 for r in ra if r.get("solved") and r["nguồn_dấu"].startswith("TREO"))
    print(f"\n=== LEDGER MỚI: {len(ra)} dòng ===")
    for k, v in nguồn.most_common():
        print(f"  {k:32s} {v}")
    print(f"\nĐIỂM CHẮC (dấu thuộc về build đem nộp): {chắc}/{len(ra)}")
    if treo_giải:
        print(f"CÒN TREO: {treo_giải} bài đang giải được nhưng dấu chưa thuộc build này")
        print(f"  {treo[:12]}{' ...' if len(treo) > 12 else ''}")
    prov = {
        "khi": time.strftime("%Y-%m-%d %H:%M:%S"),
        "tên": "recount_final_cert",
        "dòng": len(ra),
        "điểm_chắc": chắc,
        "còn_treo": treo_giải,
        "nguồn_dấu": dict(nguồn),
        "ghi_chú": ("Mỗi dòng ghi rõ dấu judge của nó đến từ đâu. Dòng TREO là "
                    "dòng CHƯA được tính: đối chứng không chứng minh được build "
                    "cuối phát ra cùng chứng chỉ, và chưa chấm lại."),
    }
    (FINAL.parent / (FINAL.name + ".prov.json")).write_text(
        json.dumps(prov, ensure_ascii=False, indent=1), encoding="utf-8")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("bước", choices=["rescan", "judge", "ledger"])
    ap.add_argument("--cap", type=float, default=120.0)
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--đường", dest="duong", choices=["auto","cert","full"], default="auto")
    ap.add_argument("--lean-timeout", type=int, default=300)
    a = ap.parse_args()
    if a.bước == "rescan":
        return bước_rescan(a.cap)
    if a.bước == "judge":
        return bước_judge(a.timeout, a.limit, a.duong, a.lean_timeout)
    return bước_ledger()


if __name__ == "__main__":
    raise SystemExit(main())
