#!/usr/bin/env python3
"""CỬA DUY NHẤT để chạy một phép đo. Không có đường vòng.

    python3 .scratch/lab/measure.py --name <tên> --result <file kết quả> -- <lệnh...>

Nó cưỡng chế bốn thứ, theo đúng thứ tự:

  1. Máy phải SẠCH  — có đối thủ đang chạy thì từ chối, không "chạy nhẹ thôi";
                      rồi DỌN rác của những lượt trước bị giết (thư mục
                      artifact mồ côi, container ee-solver sống sót).
  2. ĐỘC QUYỀN      — giữ khóa máy suốt lượt; ai khác xin cũng bị từ chối;
                      và caffeinate buộc vào vòng đời lượt chạy nên máy
                      KHÔNG THỂ ngủ giữa chừng (thứ đã giết lượt 1529 bài).
  3. Cấu hình CHUẨN — sandbox docker, hạn Lean 120s (giá trị thật của ban tổ
                      chức, không bao giờ nâng cho dễ), LEAN_PATH nạp sẵn,
                      thư mục artifact riêng cho từng lượt.
  4. TỰ KHAI BÁO    — ghi <file kết quả>.prov.json: môi trường lúc đầu, tải
                      đỉnh, đối thủ đỉnh, áp lực bộ nhớ đỉnh, swap phình bao
                      nhiêu, và kết luận ĐÁNG TIN hay KHÔNG. Người đọc kết
                      quả không cần nhớ gì.
"""
from __future__ import annotations
import argparse, contextlib, json, os, pathlib, shutil, subprocess, sys, tempfile, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import lab

REPO = pathlib.Path("/Users/nhatminh/dev/active/MagmaBallz")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--name", required=True)
    ap.add_argument("--result", required=True, help="file kết quả; .prov.json ghi cạnh nó")
    ap.add_argument("--wait", type=float, default=0.0, help="giây chờ khóa; 0 = từ chối ngay")
    ap.add_argument("--reap-after", type=float, default=0.0,
                help="giết container ee-solver sống quá N giây (0 = tắt)")
    ap.add_argument("--allow-dirty", action="store_true",
                    help="chạy dù máy có đối thủ (chỉ dùng cho việc KHÔNG phải đo)")
    ap.add_argument("cmd", nargs=argparse.REMAINDER)
    args = ap.parse_args()
    cmd = [c for c in args.cmd if c != "--"]
    if not cmd:
        print("[lab] thiếu lệnh"); return 2

    rivals = lab.competing({os.getpid()}, os.getpgrp())
    if rivals and not args.allow_dirty:
        print(f"[lab] TỪ CHỐI: máy chưa sạch, đang có {rivals}")
        print("[lab] phép đo chạy cạnh việc khác là cách sinh ra số liệu giả.")
        return 3

    # máy đã xác nhận sạch -> mọi thứ còn sót lại đều là rác của lượt bị giết
    lab.sweep_stale()

    art_root = tempfile.mkdtemp(prefix="mb-lab-art-", dir="/private/tmp")
    env = dict(os.environ)
    env.pop("OPENAI_API_KEY", None); env.pop("OPENROUTER_API_KEY", None)
    env["SB_SANDBOX_MODE"] = "docker"          # đúng hộp ban tổ chức
    env["LEAN_TIMEOUT_SECONDS"] = "120"        # giá trị thật của họ, KHÔNG nâng
    env["JUDGE_ARTIFACT_DIR"] = art_root       # sạch từng lượt
    lp = REPO / ".scratch/release/lean_path.txt"
    if lp.exists():
        env["JUDGE_LEAN_PATH"] = lp.read_text().strip()
    env["MB_LAB_WORKERS"] = str(lab.plan_workers())

    result = pathlib.Path(args.result)
    prov = result.with_suffix(result.suffix + ".prov.json")
    t0 = time.time()
    try:
        reaper = (lab.ContainerReaper(args.reap_after) if args.reap_after > 0
                  else contextlib.nullcontext())
        with lab.Exclusive(args.name, wait_seconds=args.wait), lab.Caffeine(), \
                lab.LoadWatch() as watch, reaper:
            head = lab.stamp(tên=args.name, luồng=lab.plan_workers(),
                             sandbox="docker", hạn_lean=120, lệnh=" ".join(cmd)[:200])
            print(f"[lab] chạy {args.name}: {lab.plan_workers()} luồng, "
                  f"build {head['build']}, máy sạch, chặn ngủ đang bật")
            rc = subprocess.run(cmd, cwd=str(REPO), env=env).returncode
            v = watch.verdict()
    finally:
        shutil.rmtree(art_root, ignore_errors=True)

    record = {**head, "mã_thoát": rc, "giây": round(time.time() - t0, 1), **v}
    if rc == 0 and v["đáng_tin"]:
        record["kết_luận"] = "ĐÁNG TIN"
    elif not v["đáng_tin"]:
        lý_do = []
        if v["tải_đỉnh"] > v["ngưỡng"]:
            lý_do.append(f"tải đỉnh {v['tải_đỉnh']} > {v['ngưỡng']}")
        if v["đối_thủ_đỉnh"]:
            lý_do.append(f"{v['đối_thủ_đỉnh']} tiến trình tranh chấp")
        if v["số_mẫu_nguy_cấp"]:
            lý_do.append(f"{v['số_mẫu_nguy_cấp']} mẫu áp lực bộ nhớ NGUY CẤP")
        swap_phình = v["swap_đỉnh_MB"] - v["swap_đầu_MB"]
        if swap_phình >= lab.SWAP_GROWTH_LIMIT_MB:
            lý_do.append(f"swap phình {swap_phình:.0f} MB")
        record["kết_luận"] = "KHÔNG ĐÁNG TIN — " + "; ".join(lý_do)
    else:
        record["kết_luận"] = f"lệnh thoát mã {rc}"
    prov.parent.mkdir(parents=True, exist_ok=True)
    prov.write_text(json.dumps(record, ensure_ascii=False, indent=1))
    print(f"[lab] {args.name}: {record['kết_luận']} | tải đỉnh {v['tải_đỉnh']}/"
          f"{v['ngưỡng']} | bộ nhớ đỉnh {v['áp_lực_bộ_nhớ_đỉnh']} | "
          f"swap {v['swap_đầu_MB']:.0f}->{v['swap_đỉnh_MB']:.0f} MB | dấu ghi tại {prov}")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
