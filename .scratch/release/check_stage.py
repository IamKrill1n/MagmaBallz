#!/usr/bin/env python3
"""CỔNG CHẤT LƯỢNG TỰ ĐỘNG — thay cho việc một con người (hoặc một session)
ngồi nhìn kết quả và hỏi "cái này có hợp lý không".

Mỗi chặng có một phép kiểm nội dung, không phải kiểm mã thoát. Kết quả ghi vào
STATUS.md dưới dạng con người đọc được: ĐẠT / HỎNG / NGỜ, kèm số thật.

    python3 check_stage.py <tên-chặng>     # kiểm một chặng
    python3 check_stage.py all             # kiểm hết, viết lại STATUS.md
"""
from __future__ import annotations
import json, pathlib, re, sys, datetime

REPO = pathlib.Path("/Users/nhatminh/dev/active/MagmaBallz")
S = pathlib.Path("/private/tmp/claude-501/-Users-nhatminh-dev-active-MagmaBallz/5aa77320-10be-4643-8ecb-555c1ad24f06/scratchpad")
BASELINE = 2434          # điểm đã chứng nhận trên runtime chính chủ
BASELINE_TAG = "sweep chính chủ 20/08, không LLM"


def stage_alive(name: str) -> bool:
    """Có tiến trình thật đang chạy chặng này không. Không có nó thì một log dở
    dang từ lượt đã chết sẽ bị báo là 'đang chạy' — tín hiệu sai nguy hiểm hơn
    không có tín hiệu."""
    import subprocess
    pat = {"verify":"verify_additive.py", "marathon":"run_marathon.py",
           "sweep":"scoreboard.py", "sieve":"forge_p2_sieve.py",
           "harvest":"harvest.py", "census":"route_census.py",
           "label":"label_doubt.py"}.get(name, name)
    try:
        return subprocess.run(["pgrep","-f",pat], capture_output=True).returncode == 0
    except Exception:
        return False


def read(p):
    try: return p.read_text(errors="ignore")
    except Exception: return ""


def jsonl(p):
    out = []
    for line in read(p).splitlines():
        line = line.strip()
        if line.startswith("{"):
            try: out.append(json.loads(line))
            except Exception: pass
    return out


def chk_verify():
    rows = jsonl(S/"verify_additive.ledger.jsonl") or jsonl(S/"verify_additive.log")
    if not rows: return "CHƯA CHẠY", "chưa có dữ liệu"
    keep = [r for r in rows if r.get("nhóm") == "GIỮ"]
    back = [r for r in rows if r.get("nhóm") == "VỀ"]
    ok_k = sum(1 for r in keep if r.get("judge") == "accepted")
    ok_b = sum(1 for r in back if r.get("judge") == "accepted")
    if len(keep) + len(back) < 6: return "ĐANG CHẠY", f"giữ {ok_k}/{len(keep)} về {ok_b}/{len(back)}"
    if ok_k == 3 and ok_b == 3: return "ĐẠT", "giữ 3/3, đòi lại 3/3 — lượt-4-cộng-thêm an toàn"
    return "HỎNG", (f"giữ {ok_k}/3, đòi lại {ok_b}/3 — CÓ HỒI QUY, "
                    "không được nộp build này, xem lại thiết kế cộng-thêm")


def chk_marathon():
    txt = read(S/"marathon_100.log")
    if not txt.strip(): return "CHƯA CHẠY", "chưa có log"
    if re.search(r"Traceback|No such file|error:", txt, re.I) and "accepted" not in txt.lower():
        return "HỎNG", "log có lỗi — Marathon KHÔNG chạy được, cả một track đang mất điểm"
    m = re.findall(r"(\d+)\s*/\s*(\d+)", txt)
    if m:
        a, b = max(((int(x), int(y)) for x, y in m), key=lambda t: t[1])
        rate = 100*a/max(b, 1)
        v = "ĐẠT" if rate >= 95 else "NGỜ"
        return v, f"{a}/{b} = {rate:.1f}% (kỳ vọng ≥95% — Solo cùng đề đạt ~99%)"
    return "NGỜ", "chạy xong nhưng không đọc được điểm — kiểm tay marathon_100.log"


def chk_sweep():
    rows = jsonl(S/"results/final_cert.jsonl")
    if not rows: return "CHƯA CHẠY", "chưa có kết quả"
    solved = sum(1 for r in rows if r.get("solved"))
    if len(rows) < 2469: return "ĐANG CHẠY", f"{len(rows)}/2469, đang giải {solved}"
    if solved < BASELINE:
        return "HỎNG", (f"{solved}/2469 — THẤP HƠN nền {BASELINE} ({BASELINE_TAG}). "
                        "HỒI QUY. Không nộp. Tìm bài mất bằng cách diff với official_full.jsonl")
    return "ĐẠT", f"{solved}/2469 (nền {BASELINE}, chênh {solved-BASELINE:+d})"


def chk_sieve():
    txt = read(S/"sieve3.log")
    if not txt.strip(): return "CHƯA CHẠY", "chưa có log"
    m = re.search(r"DONE: solved=(\d+) frontier=(\d+)", txt)
    if not m:
        prog = re.findall(r"(\d+)/(\d+) solved=(\d+) frontier=(\d+)", txt)
        if prog: return "ĐANG CHẠY", f"{prog[-1][0]}/{prog[-1][1]}, frontier={prog[-1][3]}"
        return "ĐANG CHẠY", "chưa có mốc tiến độ"
    fr = int(m.group(2))
    return ("ĐẠT" if fr > 0 else "NGỜ"), f"frontier={fr} cặp (0 nghĩa là đề chế ra quá dễ, phải chỉnh máy sinh)"


def chk_harvest():
    rows = jsonl(REPO/".scratch/ml/train_rows.jsonl")
    if not rows: return "CHƯA CHẠY", "chưa có dòng huấn luyện"
    pos = sum(1 for r in rows if r.get("y") == 1)
    neg = len(rows) - pos
    done = "HARVEST DONE" in read(REPO/".scratch/ml/harvest.log")
    if pos == 0: return "HỎNG", "0 nhãn dương — nhãn đang sai, mô hình sẽ vô nghĩa"
    v = "ĐẠT" if done else "ĐANG CHẠY"
    return v, f"{len(rows):,} dòng | dương {pos:,} âm {neg:,} (tỉ lệ {100*pos/len(rows):.1f}%)"


def chk_census():
    txt = read(S/"route_census.log")
    if "ROUTE CENSUS DONE" in txt: 
        fams = re.findall(r"^\s+(\S+)\s+(\d+) bài", txt, re.M)
        return "ĐẠT", f"{len(fams)} họ route, lớn nhất: {fams[0][0] if fams else '?'}"
    if txt.strip(): return "ĐANG CHẠY", (re.findall(r'"done": (\d+)', txt) or ["?"])[-1] + "/220"
    return "CHƯA CHẠY", ""


def chk_label():
    txt = read(S/"label_doubt.log")
    if not txt.strip(): return "CHƯA CHẠY", ""
    if '"CHUNG_MINH": true' in txt.lower().replace("True","true"):
        return "ĐẠT", "CÓ BÀI CHỨNG MINH ĐƯỢC — nhãn corpus sai, đây là điểm miễn phí"
    n = txt.count("CHUNG_MINH")
    return ("ĐẠT" if "LABEL DOUBT DONE" in txt else "ĐANG CHẠY"), f"{n} cấu hình đã thử, chưa cái nào ra"


PROV = {"verify": S/"verify_additive.ledger.jsonl.prov.json",
        "marathon": S/"marathon_100.log.prov.json",
        "sweep": S/"results/final_cert.jsonl.prov.json",
        "sieve": S/"sieve3.log.prov.json",
        "harvest": REPO/".scratch/ml/train_rows.jsonl.prov.json",
        "census": S/"route_census.log.prov.json",
        "label": S/"label_doubt.log.prov.json"}


def provenance(name: str):
    """Dấu môi trường do phòng thí nghiệm ghi. Không có dấu = đo bằng đường
    vòng, không qua cửa lab -> cũng không đáng tin."""
    p = PROV.get(name)
    if p is None or not p.exists():
        return None
    try:
        return json.loads(p.read_text())
    except Exception:
        return None


CHECKS = [("verify", chk_verify, "phép thử hồi quy — CHẶN NỘP nếu hỏng"),
          ("marathon", chk_marathon, "đường đua thứ hai"),
          ("sweep", chk_sweep, "điểm chứng nhận — CHẶN NỘP nếu hỏng"),
          ("sieve", chk_sieve, "chế đề khó cho Forge"),
          ("harvest", chk_harvest, "dữ liệu huấn luyện ML"),
          ("census", chk_census, "phân bố route"),
          ("label", chk_label, "nghi vấn nhãn corpus")]


def main():
    want = sys.argv[1] if len(sys.argv) > 1 else "all"
    lines, blockers = [], []
    for name, fn, desc in CHECKS:
        if want not in ("all", name): continue
        try: verdict, detail = fn()
        except Exception as exc: verdict, detail = "HỎNG", f"phép kiểm lỗi: {exc!r}"
        pr = provenance(name)
        if verdict in ("ĐẠT", "NGỜ") and pr is not None and not pr.get("đáng_tin", True):
            verdict = "NGỜ"
            detail += (f" | ⚠️ ĐO TRONG TRANH CHẤP: tải đỉnh {pr.get('tải_đỉnh')}"
                       f"/{pr.get('ngưỡng')}, đối thủ {pr.get('đối_thủ_đỉnh')} — số này KHÔNG dùng được")
        elif verdict == "ĐẠT" and pr is not None:
            detail += f" | môi trường sạch, build {pr.get('build')}, {pr.get('luồng')} luồng"
        if verdict == "ĐANG CHẠY" and not stage_alive(name):
            verdict = "DỞ DANG"      # log có nhưng không tiến trình nào sống
        mark = {"ĐẠT":"✅","HỎNG":"❌","NGỜ":"⚠️","ĐANG CHẠY":"⏳",
                "DỞ DANG":"◐","CHƯA CHẠY":"·"}[verdict]
        lines.append(f"| {mark} {name} | {verdict} | {detail} |")
        if verdict == "HỎNG": blockers.append(f"{name}: {detail}")
        if want == name: print(f"{mark} {name}: {verdict} — {detail}")
    if want != "all": return
    stamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M")
    body = [f"# TRẠNG THÁI — tự sinh lúc {stamp}", "",
            "Sinh bởi `.scratch/release/check_stage.py`. Đây là **kiểm nội dung**, không phải",
            "kiểm mã thoát: mỗi chặng bị hỏi 'kết quả có hợp lý không', không phải 'có chạy không'.",
            "", "| Chặng | Kết luận | Chi tiết |", "|---|---|---|", *lines, ""]
    if blockers:
        body += ["## ⛔ CHẶN NỘP BÀI", ""] + [f"- {b}" for b in blockers] + [""]
    else:
        body += ["Không có chặng nào HỎNG.", ""]
    (REPO/".scratch/release/STATUS.md").write_text("\n".join(body))
    print("\n".join(body))


if __name__ == "__main__":
    main()
