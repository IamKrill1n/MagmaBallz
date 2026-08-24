# CỔNG VERIFY CỘNG-THÊM — tái dựng 25/08 sau khi bản gốc trong scratchpad
# /private/tmp bị dọn mất. Hợp đồng giữ nguyên theo ledger cũ:
#   - 3 bài GIỮ  (hard3_0131, hard3_0214, hard3_0266): build từng ăn, không được mất
#   - 3 bài VỀ   (hard2_0028, normal_0062, normal_0492): bài đòi lại, phải còn ăn
#   - ghi từng dòng jsonl {id, nhóm, route, judge, s} + "KETQUA giữ=x/3 về=y/3"
#   - kết thúc bằng "VERIFY ADDITIVE DONE"
# Kết quả ghi vào file do measure.py chỉ định qua RESULT (biến môi trường),
# mặc định $SCRATCH cũ để tương thích run_chain.
import importlib.util
import json
import os
import pathlib
import sys
import time

REPO = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO))
sys.path.insert(0, str(REPO / ".scratch/release"))

import judge_lock  # noqa: E402
from pipeline.proxy import DEFAULT_PROOF_POLICY  # noqa: E402

spec = importlib.util.spec_from_file_location("solver", REPO / "EQT02-M00006.py")
solver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(solver)

CASES = [
    ("hard3_0131", "GIỮ"), ("hard3_0214", "GIỮ"), ("hard3_0266", "GIỮ"),
    ("hard2_0028", "VỀ"), ("normal_0062", "VỀ"), ("normal_0492", "VỀ"),
]

RESULT = os.environ.get(
    "VERIFY_LEDGER",
    "/private/tmp/claude-501/-Users-nhatminh-dev-active-MagmaBallz/"
    "5aa77320-10be-4643-8ecb-555c1ad24f06/scratchpad/verify_additive.ledger.jsonl")

problems = {}
import glob
for path in glob.glob(str(REPO / "examples/problems/*.jsonl")):
    for line in open(path, encoding="utf-8"):
        r = json.loads(line)
        problems[r["id"]] = r

keep = back = 0
with open(RESULT, "a", encoding="utf-8") as ledger:
    for pid, group in CASES:
        rec = problems[pid]
        t0 = time.time()
        route = verdict = None
        try:
            out = solver.solve_problem(rec, false_time_budget=120.0)
        except Exception:
            out = None
        if out:
            route = out["route"]
            rec2 = dict(rec)
            rec2["proof_policy"] = DEFAULT_PROOF_POLICY
            try:
                jr = judge_lock.judged(rec2, out["answer"]["verdict"],
                                       out["answer"]["code"])
                verdict = jr.get("status")
            except Exception:
                verdict = "judge_error"
        row = {"id": pid, "nhóm": group, "route": route, "judge": verdict,
               "s": round(time.time() - t0, 1)}
        ledger.write(json.dumps(row, ensure_ascii=False) + "\n")
        ledger.flush()
        print(json.dumps(row, ensure_ascii=False), flush=True)
        if verdict == "accepted":
            if group == "GIỮ":
                keep += 1
            else:
                back += 1
print(f"KETQUA giữ={keep}/3 về={back}/3")
print("VERIFY ADDITIVE DONE")
