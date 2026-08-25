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
  3. Cấu hình CHUẨN — sandbox docker, LEAN_PATH nạp sẵn, thư mục artifact
                      riêng cho từng lượt, và hạn Lean được ĐỌC RA từ mã ban
                      tổ chức rồi đóng vào dấu (300 s trên đường Solo) thay vì
                      bịa một con số rồi khai như thật.
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
    ap.add_argument("--solver-dir", default=None,
                    help="chép EQT02-M00006.py của repo vào <dir>/solver.py rồi "
                         "khai mã băm ra dấu — chặn việc đo nhầm build cũ")
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

    sync = lab.sync_solver(args.solver_dir) if args.solver_dir else {}
    if sync:
        print(f"[lab] đồng bộ build vào {args.solver_dir}: "
              f"sha={sync['solver_sha']} {sync['solver_byte']} byte")

    art_root = tempfile.mkdtemp(prefix="mb-lab-art-", dir="/private/tmp")
    env = dict(os.environ)
    env.pop("OPENAI_API_KEY", None); env.pop("OPENROUTER_API_KEY", None)
    env["SB_SANDBOX_MODE"] = "docker"          # đúng hộp ban tổ chức
    # Chỉ có tác dụng với lời gọi judge TRỰC TIẾP (harness, challenger); trên
    # đường pipeline proxy truyền hạn tường minh từ config.json nên biến này
    # bị bỏ qua. Đặt bằng đúng giá trị pipeline để hai đường không lệch nhau.
    hạn = lab.lean_timeout_thật()
    env["LEAN_TIMEOUT_SECONDS"] = str(hạn["hạn_lean_pipeline"] or 300)
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
                             sandbox="docker", **hạn,
                             lệnh=" ".join(cmd)[:200], **sync)
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
        if v["tỉ_lệ_vượt_tải"] > lab.DIRTY_FRACTION_LIMIT:
            lý_do.append(f"{v['mẫu_vượt_tải']}/{v['số_mẫu']} mẫu "
                         f"({v['tỉ_lệ_vượt_tải']:.1%}) vượt tải {v['ngưỡng']}")
        if v["tải_đỉnh"] > v["ngưỡng"] * lab.SEVERE_SPIKE_RATIO:
            lý_do.append(f"cơn tải cực nặng, đỉnh {v['tải_đỉnh']}")
        if v["đối_thủ_đỉnh"]:
            lý_do.append(f"{v['đối_thủ_đỉnh']} tiến trình tranh chấp")
        if v["tỉ_lệ_nguy_cấp"] > lab.DIRTY_FRACTION_LIMIT:
            lý_do.append(f"{v['số_mẫu_nguy_cấp']}/{v['số_mẫu']} mẫu "
                         f"({v['tỉ_lệ_nguy_cấp']:.1%}) áp lực bộ nhớ NGUY CẤP")
        swap_phình = v["swap_đỉnh_MB"] - v["swap_đầu_MB"]
        if swap_phình >= lab.SWAP_GROWTH_LIMIT_MB:
            lý_do.append(f"swap phình {swap_phình:.0f} MB")
        record["kết_luận"] = "KHÔNG ĐÁNG TIN — " + "; ".join(lý_do)
    else:
        record["kết_luận"] = f"lệnh thoát mã {rc}"
    prov.parent.mkdir(parents=True, exist_ok=True)
    prov.write_text(json.dumps(record, ensure_ascii=False, indent=1))
    print(f"[lab] {args.name}: {record['kết_luận']} | tải đỉnh {v['tải_đỉnh']}/"
          f"{v['ngưỡng']} ({v['mẫu_vượt_tải']}/{v['số_mẫu']} mẫu vượt) | bộ nhớ đỉnh {v['áp_lực_bộ_nhớ_đỉnh']} | "
          f"swap {v['swap_đầu_MB']:.0f}->{v['swap_đỉnh_MB']:.0f} MB | dấu ghi tại {prov}")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
