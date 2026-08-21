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
import contextlib, glob, json, os, pathlib, shutil, subprocess, threading, time

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
# Swap phình quá mức này giữa lượt đo nghĩa là máy đã tráo trang: Lean bị bỏ
# đói y hệt lúc quá tải luồng, và mọi `incorrect` sinh ra đều đáng ngờ.
SWAP_GROWTH_LIMIT_MB = 2048.0
# Phán "đáng tin" theo TỈ LỆ mẫu bẩn, không theo đỉnh. Một lượt 11 tiếng có
# ~2000 mẫu; nếu một cơn tải thoáng qua (Spotlight, backup, người dùng mở
# app) đủ kết án cả lượt thì cái dấu kêu oan quá dễ và thành vô dụng — không
# ai còn tin nó, đúng cái bệnh nó sinh ra để chữa. Nhưng một cơn CỰC nặng
# thì vẫn kết án, dù ngắn: lúc đó Lean đã bị bỏ đói thật.
DIRTY_FRACTION_LIMIT = 0.02   # quá 2% số mẫu vượt ngưỡng -> không đáng tin
SEVERE_SPIKE_RATIO = 1.5      # đỉnh vượt 1,5 lần ngưỡng -> không đáng tin ngay

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
            if _is_shell_wrapper(pid):
                continue
            found.append(f"{pat}:{pid}")
    return found


def _is_shell_wrapper(pid: int) -> bool:
    """Tiến trình vỏ chỉ NHẮC tên kịch bản trong dòng lệnh, không chạy nó.

    Đo 22/08: vòng chờ `until ! pgrep -f "scoreboard.py ..."` khiến chính
    tiến trình bash đó mang chuỗi "scoreboard.py" trong argv, nên bộ dò tính
    nó là đối thủ và đóng dấu KHÔNG ĐÁNG TIN cho một lượt đo hoàn toàn sạch.
    Cái dấu báo động giả thì cũng vô dụng như cái dấu im lặng."""
    try:
        r = subprocess.run(["ps", "-o", "comm=", "-p", str(pid)],
                           capture_output=True, text=True, timeout=10)
    except Exception:
        return False
    comm = r.stdout.strip().rsplit("/", 1)[-1]
    return comm in {"bash", "sh", "zsh", "pgrep", "grep", "ps", "tail", "sleep"}


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


def mem_pressure() -> int:
    """Mức áp lực bộ nhớ theo chính macOS: 1 bình thường, 2 cảnh báo, 4 nguy cấp.

    Đây là tín hiệu đúng chứ không phải "còn bao nhiêu MB trống": macOS giữ
    RAM gần đầy theo thiết kế, nên số MB trống thấp là bình thường, còn mức
    áp lực mới là lúc nó bắt đầu nén và tráo trang ra đĩa."""
    try:
        r = subprocess.run(["sysctl", "-n", "kern.memorystatus_vm_pressure_level"],
                           capture_output=True, text=True, timeout=10)
        return int(r.stdout.strip() or 1)
    except Exception:
        return 1


def swap_used_mb() -> float:
    """MB swap đang dùng. Swap phình lên giữa lượt đo là dấu hiệu máy đang
    tráo trang — chính là thứ bỏ đói Lean và làm nó vượt hạn 120 s, rồi
    judge ghi certificate ĐÚNG thành SAI."""
    try:
        r = subprocess.run(["sysctl", "-n", "vm.swapusage"],
                           capture_output=True, text=True, timeout=10)
        for tok in r.stdout.replace("=", " ").split():
            if tok.endswith("M") and tok[0].isdigit():
                return float(tok[:-1])
    except Exception:
        pass
    return 0.0


def sweep_stale(verbose: bool = True) -> dict:
    """Dọn rác của những lượt trước BỊ GIẾT.

    measure.py chỉ xóa thư mục artifact khi thoát bình thường; lượt bị Ctrl-C
    hay kill -9 để lại nguyên. Container ee-solver cũng sống sót khi lệnh
    docker phía host chết. Cả hai đều tích lại rồi ăn đĩa và RAM của lượt sau.

    Chỉ gọi SAU khi đã xác nhận máy sạch: lúc đó mọi thứ còn sót đều là rác
    theo định nghĩa, không phải của ai đang chạy."""
    out = {"thư_mục_rác": 0, "container_rác": 0}
    for d in glob.glob("/private/tmp/mb-lab-art-*"):
        # phải xử cả file lẫn thư mục: rmtree lặng lẽ bỏ qua file, nên bản
        # chỉ-rmtree vừa để sót rác vừa BÁO LÀ ĐÃ DỌN — đúng cái kiểu tự khai
        # sai mà cả lớp hạ tầng này sinh ra để chặn
        try:
            if os.path.isdir(d):
                shutil.rmtree(d, ignore_errors=True)
            else:
                os.unlink(d)
            out["thư_mục_rác"] += 1
        except Exception:
            pass
    try:
        r = subprocess.run(["docker", "ps", "-aq", "--filter", "name=ee-solver"],
                           capture_output=True, text=True, timeout=30)
        names = [x for x in r.stdout.split() if x]
        if names:
            subprocess.run(["docker", "rm", "-f", *names],
                           capture_output=True, timeout=120)
            out["container_rác"] = len(names)
    except Exception:
        pass
    if verbose and (out["thư_mục_rác"] or out["container_rác"]):
        print(f"[lab] dọn rác lượt trước: {out['thư_mục_rác']} thư mục artifact, "
              f"{out['container_rác']} container", flush=True)
    return out


def lean_timeout_thật() -> dict:
    """Hạn Lean THẬT trên đường chấm Solo, đọc từ mã ban tổ chức.

    Đây là chỗ tôi từng tự lừa mình: measure.py ép LEAN_TIMEOUT_SECONDS=120
    rồi đóng dấu "hạn_lean=120". Nhưng proxy truyền hạn XUỐNG judge bằng
    tham số tường minh lấy từ pipeline/config.json (300 s), và judge chỉ đọc
    biến môi trường ở nhánh config=None — nhánh bị bỏ qua. Nên biến môi
    trường ấy VÔ HIỆU trên đường pipeline, còn cái dấu thì khai sai suốt.

    Chú thích của chính ban tổ chức ở proxy.py:985 nói rõ:
    "gets the 300 s the contestant was promised, never more."
    Hạn cuối là min(config, thời gian còn lại của bài) — nên bài tiêu gần
    hết ngân sách trước khi chấm sẽ để judge ít giây hơn hẳn."""
    out = {"hạn_lean_pipeline": None, "hạn_lean_judge_mặc_định": None}
    try:
        cfg = json.loads((REPO / "pipeline/config.json").read_text())
        out["hạn_lean_pipeline"] = int(cfg["judge"]["lean_timeout_seconds"])
    except Exception:
        pass
    try:
        for line in (REPO / "judge/verify.py").read_text().splitlines():
            if line.startswith("LEAN_TIMEOUT_SECONDS"):
                out["hạn_lean_judge_mặc_định"] = int(line.split("=")[1].strip())
                break
    except Exception:
        pass
    return out


def file_sha(path) -> str:
    import hashlib
    try:
        return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()[:12]
    except Exception:
        return "?"


def sync_solver(sub_dir) -> dict:
    """Đồng bộ build trong repo vào thư mục nộp bài RỒI khai băm ra dấu.

    Sandbox gắn thư mục nộp bài (-v <dir>:/solver:ro), nên phép đo chạy
    solver.py trong ĐÓ, không phải file trong repo. Ngày 21/08 kiểm ra thì
    cả 20 thư mục nộp bài đều là bản cũ — phóng sweep lúc đó là đo nhầm
    build mà không có gì báo. Nay việc chép là bắt buộc và mã băm nằm trong
    prov.json, nên câu 'lượt này đo build nào' không còn phải nhớ."""
    sub_dir = pathlib.Path(sub_dir)
    sub_dir.mkdir(parents=True, exist_ok=True)
    src = REPO / "EQT02-M00006.py"
    dst = sub_dir / "solver.py"
    shutil.copy2(src, dst)
    return {"solver_sha": file_sha(dst), "solver_byte": dst.stat().st_size,
            "solver_từ": str(src), "solver_tới": str(dst)}


class Caffeine:
    """Chặn máy ngủ suốt lượt đo, buộc vào vòng đời của chính tiến trình này.

    Ngày 20/08 mất trắng một lượt 1529 bài vì máy ngủ bốn lần khi chạy pin,
    đẻ ra 6 thất bại hard3 GIẢ. Lần đó tôi quên bật caffeinate. Nên nó không
    còn là thứ phải nhớ nữa: `-w <pid>` khiến caffeinate tự chết theo phép đo,
    không bao giờ sống sót thành tiến trình mồ côi ghim máy thức mãi.

    Bản thân caffeinate tốn 0,0% CPU nên không hề chen vào phép đo."""

    def __init__(self, pid: int | None = None):
        self.pid = pid or os.getpid()
        self.proc = None

    def __enter__(self):
        try:
            self.proc = subprocess.Popen(
                ["caffeinate", "-dims", "-w", str(self.pid)],
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        except Exception as exc:
            print(f"[lab] CẢNH BÁO: không bật được caffeinate ({exc}) — "
                  "máy có thể ngủ và làm hỏng lượt đo", flush=True)
        return self

    def __exit__(self, *exc):
        if self.proc is not None:
            with contextlib.suppress(Exception):
                self.proc.terminate()
        return False


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
        self.over_limit = 0               # số mẫu tải vượt ngưỡng
        self.mem_peak = 1                 # mức áp lực bộ nhớ cao nhất gặp phải
        self.mem_critical = 0             # số mẫu ở mức nguy cấp
        self.swap0 = swap_used_mb()
        self.swap_peak = self.swap0
        self._stop = threading.Event()
        self._t = threading.Thread(target=self._run, daemon=True)

    def _run(self):
        limit = cores() * LOAD_SAFE_RATIO
        while not self._stop.wait(self.period):
            l1 = load1()
            self.peak = max(self.peak, l1)
            if l1 > limit:
                self.over_limit += 1
            self.max_rivals = max(self.max_rivals,
                                  len(competing({os.getpid()}, self.own_pgid)))
            lvl = mem_pressure()
            self.mem_peak = max(self.mem_peak, lvl)
            if lvl >= 4:
                self.mem_critical += 1
                if self.mem_critical in (1, 5, 20):
                    print(f"[lab] CẢNH BÁO: áp lực bộ nhớ NGUY CẤP "
                          f"(mẫu thứ {self.mem_critical}) — kết quả trong khoảng "
                          "này sẽ bị đánh dấu không đáng tin", flush=True)
            self.swap_peak = max(self.swap_peak, swap_used_mb())
            self.samples += 1

    def __enter__(self):
        self._t.start()
        return self

    def __exit__(self, *exc):
        self._stop.set()
        return False

    def verdict(self) -> dict:
        limit = cores() * LOAD_SAFE_RATIO
        n = max(1, self.samples)
        tỉ_lệ_tải = self.over_limit / n
        tỉ_lệ_nhớ = self.mem_critical / n
        swap_growth = self.swap_peak - self.swap0
        clean = (
            tỉ_lệ_tải <= DIRTY_FRACTION_LIMIT
            and self.peak <= limit * SEVERE_SPIKE_RATIO
            and tỉ_lệ_nhớ <= DIRTY_FRACTION_LIMIT
            and self.max_rivals == 0
            and swap_growth < SWAP_GROWTH_LIMIT_MB
        )
        return {"tải_đỉnh": round(self.peak, 2), "ngưỡng": round(limit, 2),
                "mẫu_vượt_tải": self.over_limit,
                "tỉ_lệ_vượt_tải": round(tỉ_lệ_tải, 4),
                "đối_thủ_đỉnh": self.max_rivals, "số_mẫu": self.samples,
                "áp_lực_bộ_nhớ_đỉnh": self.mem_peak,
                "số_mẫu_nguy_cấp": self.mem_critical,
                "tỉ_lệ_nguy_cấp": round(tỉ_lệ_nhớ, 4),
                "swap_đầu_MB": round(self.swap0, 1),
                "swap_đỉnh_MB": round(self.swap_peak, 1),
                "đáng_tin": clean}


def stamp(**extra) -> dict:
    return {"khi": time.strftime("%Y-%m-%d %H:%M:%S"),
            "lõi": cores(), "tải_đầu": round(load1(), 2),
            "đối_thủ_đầu": competing({os.getpid()}, os.getpgrp()),
            "container_đầu": docker_containers(),
            "áp_lực_bộ_nhớ_đầu": mem_pressure(), "swap_đầu": round(swap_used_mb(), 1),
            "build": build_commit(), **extra}


class ContainerReaper:
    """Giết container ee-solver sống quá hạn.

    Đo được 21/08: harness đặt hạn 600 s mỗi bài, nhưng khi solver bên trong
    container không tự dừng thì container SỐNG TIẾP — quan sát được một cái
    chạy 3 tiếng, và cả lượt sweep đứng im chờ nó: 4/2469 bài sau 3 giờ. Lệnh
    docker phía host bị giết không kéo theo container.

    Đây là chốt chặn phía mình, không đụng mã ban tổ chức: quá hạn cộng biên
    thì giết thẳng, để phép đo đi tiếp thay vì treo vô hạn.
    """

    def __init__(self, max_age_seconds: float, period: float = 30.0):
        self.max_age, self.period = max_age_seconds, period
        self.killed = 0
        self._stop = threading.Event()
        self._t = threading.Thread(target=self._run, daemon=True)

    def _ages(self):
        try:
            r = subprocess.run(
                ["docker", "ps", "--filter", "name=ee-solver",
                 "--format", "{{.Names}}\t{{.RunningFor}}"],
                capture_output=True, text=True, timeout=20)
        except Exception:
            return []
        out = []
        for line in r.stdout.splitlines():
            if "\t" not in line:
                continue
            name, ago = line.split("\t", 1)
            secs = 0.0
            low = ago.lower()
            for unit, mult in (("second", 1), ("minute", 60), ("hour", 3600), ("day", 86400)):
                if unit in low:
                    num = "".join(ch for ch in low.split(unit)[0] if ch.isdigit())
                    secs = float(num or 1) * mult
                    break
            out.append((name, secs))
        return out

    def _run(self):
        while not self._stop.wait(self.period):
            for name, age in self._ages():
                if age > self.max_age:
                    try:
                        subprocess.run(["docker", "kill", name],
                                       capture_output=True, timeout=30)
                        self.killed += 1
                        print(f"[lab] thu hồi container quá hạn: {name} ({age:.0f}s)",
                              flush=True)
                    except Exception:
                        pass

    def __enter__(self):
        self._t.start()
        return self

    def __exit__(self, *exc):
        self._stop.set()
        return False
