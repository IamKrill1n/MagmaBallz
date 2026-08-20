#!/usr/bin/env python3
"""PHÒNG THÍ NGHIỆM — hạ tầng cho phép đo cô lập và tái lập được.

Ngày 20/08 mất bảy lần vì cùng một gốc: không ai làm chủ tài nguyên máy, mọi
thứ cứ khởi động rồi hy vọng. Hậu quả đều cùng một dạng — một build TỐT trông
như HỎNG, rồi tôi đi sửa nhầm chỗ:

  · chấm song song cùng một bài  -> giẫm thư mục artifact -> `incorrect` giả
  · lệnh chấm tay chen ngang sweep -> hỏng phán quyết bài khác
  · ba luồng docker              -> Lean bị bỏ đói, vượt hạn 120s
                                    -> judge ghi certificate ĐÚNG là SAI

Thiết kế này không dựa vào ai nhớ luật. Ba tính chất được CƯỠNG CHẾ:

  1. ĐỘC QUYỀN      Phép đo phải giữ khóa máy. Không giữ được thì KHÔNG CHẠY,
                    chứ không "chạy nhẹ thôi".
  2. KHÔNG BỘI CUNG Số luồng TÍNH từ số lõi thật và chi phí thật, không chọn
                    tay. Mặc định cực bảo thủ: thà chậm còn hơn sai.
  3. TỰ KHAI BÁO    Kết quả nào sinh ra trong lúc tranh chấp thì TỰ mang dấu
                    không đáng tin — không phụ thuộc việc ai đó nhớ nhìn.
"""
from __future__ import annotations
import json, os, pathlib, subprocess, threading, time

LAB = pathlib.Path("/private/tmp/magmaballz-lab")
LAB.mkdir(parents=True, exist_ok=True)
LOCK = LAB / "machine.lock"
REPO = pathlib.Path("/Users/nhatminh/dev/active/MagmaBallz")

# Chi phí THẬT của một đơn vị việc đo, tính bằng lõi:
#   container solver 2 CPU  +  Lean lúc biên dịch (đa luồng, tới ~4 lõi đỉnh)
# Đặt bảo thủ: thà thừa chỗ còn hơn bỏ đói Lean rồi nhận `incorrect` giả.
CORES_PER_WORKER = 6
CORES_RESERVED = 2            # chừa cho hệ điều hành và người dùng
LOAD_SAFE_RATIO = 0.85        # tải1/lõi vượt mức này -> coi là tranh chấp

RIVALS = ("scoreboard.py", "run_marathon.py", "verify_additive.py", "harvest.py",
          "forge_p2_sieve.py", "route_census.py", "label_doubt.py", "recalib_check.py",
          "neversolved.py", "enum_attack.py", "heavy_attack.py", "eval_attack.py",
          "anneal_false.py", "calib_prior.py")


def cores() -> int:
    return os.cpu_count() or 4


def load1() -> float:
    try:
        return os.getloadavg()[0]
    except Exception:
        return 0.0


def _pgid(pid: int) -> int | None:
    try:
        return os.getpgid(pid)
    except Exception:
        return None


def competing(exclude_pids: set[int] | None = None,
              exclude_pgid: int | None = None) -> list[str]:
    """Tiến trình đo KHÁC đang tranh tài nguyên.

    Lọc theo NHÓM TIẾN TRÌNH, không chỉ theo pid: con cháu do chính phép đo
    này sinh ra không phải đối thủ của nó. Thiếu chỗ này thì mọi phép đo tự
    khai là bẩn và cái dấu trở nên vô nghĩa."""
    exclude_pids = exclude_pids or set()
    found = []
    for pat in RIVALS:
        try:
            r = subprocess.run(["pgrep", "-f", pat], capture_output=True, text=True)
        except Exception:
            continue
        for pid_s in r.stdout.split():
            pid = int(pid_s)
            if pid in exclude_pids:
                continue
            if exclude_pgid is not None and _pgid(pid) == exclude_pgid:
                continue
            found.append(f"{pat}:{pid}")
    return found


def plan_workers(cores_per_worker: int = CORES_PER_WORKER) -> int:
    """Số luồng TÍNH RA. Máy 10 lõi, mỗi đơn vị 6 lõi, chừa 2 -> 1 luồng.
    Con số 3 chọn tay chính là thứ đã bỏ đói Lean ngày 20/08."""
    return max(1, (cores() - CORES_RESERVED) // cores_per_worker)


def build_commit() -> str:
    try:
        return subprocess.run(["git", "-C", str(REPO), "rev-parse", "--short", "HEAD"],
                              capture_output=True, text=True).stdout.strip() or "?"
    except Exception:
        return "?"


def docker_containers() -> int:
    try:
        r = subprocess.run(["docker", "ps", "-q", "--filter", "name=ee-solver"],
                           capture_output=True, text=True)
        return len([x for x in r.stdout.split() if x])
    except Exception:
        return 0


class Exclusive:
    """Khóa máy độc quyền — điểm khác biệt với 'cố gắng đừng chạy chồng' là
    không giữ được khóa thì phép đo KHÔNG chạy chút nào."""

    def __init__(self, name: str, wait_seconds: float = 0.0):
        self.name, self.wait = name, wait_seconds

    def __enter__(self):
        deadline = time.time() + self.wait
        while True:
            try:
                fd = os.open(str(LOCK), os.O_CREAT | os.O_EXCL | os.O_WRONLY)
                os.write(fd, json.dumps({"tên": self.name, "pid": os.getpid(),
                                         "từ": time.time()}).encode())
                os.close(fd)
                return self
            except FileExistsError:
                try:
                    held = json.loads(LOCK.read_text())
                    os.kill(int(held["pid"]), 0)
                except Exception:
                    LOCK.unlink(missing_ok=True)
                    continue                       # khóa mồ côi sau mất điện
                if time.time() >= deadline:
                    raise SystemExit(
                        f"[lab] máy đang bận: {held.get('tên')} (pid {held.get('pid')}). "
                        "KHÔNG chạy phép đo — chạy chồng là cách sinh ra số liệu giả.")
                time.sleep(5.0)

    def __exit__(self, *exc):
        LOCK.unlink(missing_ok=True)
        return False


class LoadWatch:
    """Lấy mẫu tải suốt lượt chạy. Đỉnh vượt ngưỡng -> kết quả tự mang dấu
    không đáng tin. Đây là trụ quan trọng nhất: cả ba lần bị lừa hôm nay đều
    do con số trông hợp lý trong khi môi trường thì bẩn."""

    def __init__(self, period: float = 20.0, own_pgid: int | None = None):
        self.period, self.peak, self.samples = period, 0.0, 0
        self.own_pgid = own_pgid if own_pgid is not None else os.getpgrp()
        self.max_rivals = 0
        self._stop = threading.Event()
        self._t = threading.Thread(target=self._run, daemon=True)

    def _run(self):
        while not self._stop.wait(self.period):
            self.peak = max(self.peak, load1())
            self.max_rivals = max(self.max_rivals,
                                  len(competing({os.getpid()}, self.own_pgid)))
            self.samples += 1

    def __enter__(self):
        self._t.start()
        return self

    def __exit__(self, *exc):
        self._stop.set()
        return False

    def verdict(self) -> dict:
        limit = cores() * LOAD_SAFE_RATIO
        clean = (self.peak <= limit) and (self.max_rivals == 0)
        return {"tải_đỉnh": round(self.peak, 2), "ngưỡng": round(limit, 2),
                "đối_thủ_đỉnh": self.max_rivals, "số_mẫu": self.samples,
                "đáng_tin": clean}


def stamp(**extra) -> dict:
    return {"khi": time.strftime("%Y-%m-%d %H:%M:%S"),
            "lõi": cores(), "tải_đầu": round(load1(), 2),
            "đối_thủ_đầu": competing({os.getpid()}, os.getpgrp()),
            "container_đầu": docker_containers(),
            "build": build_commit(), **extra}
