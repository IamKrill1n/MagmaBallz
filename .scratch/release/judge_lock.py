"""Khóa chấm bài theo TỪNG BÀI — bắt buộc dùng thay cho verify_answer trần.

Judge tạo thư mục artifact theo băm (bài + mã), nên HAI lượt chấm cùng một bài
cùng lúc sẽ giẫm lên nhau và sinh ra kết quả rác: đã đo được `incorrect` cho
một certificate mà chạy riêng thì `accepted`, và cả lỗi hạ tầng
"Lean finished without emitting a valid judge dependency report".

Đây là lỗi ĐỌC SAI KẾT QUẢ, không phải lỗi solver — nguy hiểm vì nó khiến ta
tưởng mình vừa làm hỏng thứ vốn đang tốt. Đã dính ba lần trong một ngày, nên
biến thành cơ chế chứ không phải kỷ luật.

Dùng:
    from judge_lock import judged
    r = judged(problem_dict, verdict, code)
"""
from __future__ import annotations
import hashlib, json, os, pathlib, sys, time

LOCK_ROOT = pathlib.Path("/private/tmp/claude-501/magmaballz-judge-locks")
LOCK_ROOT.mkdir(parents=True, exist_ok=True)
sys.path.insert(0, "/Users/nhatminh/dev/active/MagmaBallz")


SWEEP_MARKER = LOCK_ROOT / "SWEEP_RUNNING"


def sweep_active() -> bool:
    """Sweep chứng nhận có đang chạy không. Mọi lệnh chấm tay phải NHƯỜNG nó:
    Lean dùng chung thư mục build, nên một lệnh chấm chen ngang có thể làm hỏng
    phán quyết của bài KHÁC đang chấm song song. Đo được 20/8: 23 bài nền chỉ
    tốn 3-40s bỗng `incorrect` và chạm trần 600s, trong khi chạy riêng thì
    chúng `accepted` trong 0.0s."""
    import subprocess
    try:
        return subprocess.run(["pgrep", "-f", "scoreboard.py"],
                              capture_output=True).returncode == 0
    except Exception:
        return False


def judged(problem: dict, verdict: str, code: str, *, wait: float = 900.0,
           yield_to_sweep: bool = True):
    from judge.verify import verify_answer
    if yield_to_sweep:
        waited = 0.0
        while sweep_active() and waited < 7200:
            time.sleep(15.0); waited += 15.0
    key = hashlib.sha1(f"{problem.get('id')}|{code}".encode()).hexdigest()[:16]
    lock = LOCK_ROOT / key
    deadline = time.time() + wait
    while True:
        try:
            fd = os.open(str(lock), os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            os.write(fd, str(os.getpid()).encode()); os.close(fd)
            break
        except FileExistsError:
            # khóa mồ côi sau khi tiến trình chết -> thu hồi
            try:
                pid = int(lock.read_text() or 0)
                os.kill(pid, 0)
            except Exception:
                lock.unlink(missing_ok=True); continue
            if time.time() > deadline:
                lock.unlink(missing_ok=True); continue
            time.sleep(1.0)
    try:
        return verify_answer(problem, json.dumps({"verdict": verdict, "code": code}))
    finally:
        lock.unlink(missing_ok=True)
