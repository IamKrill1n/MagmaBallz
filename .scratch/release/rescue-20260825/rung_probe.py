"""Câu hỏi: động cơ bão hòa CỦA MÌNH có dựng nổi ba luật sập không, nếu được
cho ngân sách rộng rãi? Nếu CÓ -> đây là vấn đề CHÍNH SÁCH (mình không rót đủ
cho nó, đúng lúc). Nếu KHÔNG -> đây là vấn đề TẦM VỚI của động cơ."""
import importlib.util, json, pathlib, sys, time
REPO="/Users/nhatminh/dev/active/MagmaBallz"; sys.path.insert(0,REPO)
SPD="/private/tmp/claude-501/-Users-nhatminh-dev-active-MagmaBallz/5aa77320-10be-4643-8ecb-555c1ad24f06/scratchpad"
spec=importlib.util.spec_from_file_location("m6",REPO+"/EQT02-M00006.py")
m6=importlib.util.module_from_spec(spec); spec.loader.exec_module(m6)
MONG={"evaluation_order5_0016":"x = y","evaluation_order5_0028":"x ◇ y = x",
      "evaluation_order5_0152":"x ◇ y = y","hard3_0106":"x ◇ y = x",
      "hard3_0271":"x ◇ y = y","evaluation_order5_0042":None}
probs={json.loads(l)["id"]:json.loads(l) for l in open(SPD+"/corpora/gap6.jsonl")}
print(f"{'bài':<26}{'nấc':<14}{'kết quả':<34}{'giây':>7}")
for pid,q in probs.items():
    e1=m6.parse_equation(q["equation1"].replace("◇","*"))
    for rung in m6.HEAVY_LADDER_RUNGS:
        re_=m6.parse_equation(rung.replace("◇","*"))
        mods=m6.find_h_models(e1)
        if any(not m6.table_satisfies_equation(re_,t) for t in mods):
            print(f"{pid:<26}{rung:<14}{'H có mô hình phá nấc -> loại (đúng)':<34}{0:>7}")
            continue
        t0=time.time()
        try:
            r=m6.cp_saturation_route(e1, re_, lemma_budget=4000, rounds=40, time_budget=180.0)
        except Exception as exc:
            r=None; print("   lỗi",exc)
        dt=time.time()-t0
        dau = " <== reja23 dùng nấc này" if MONG.get(pid)==rung else ""
        print(f"{pid:<26}{rung:<14}{('DỰNG ĐƯỢC: '+r[0] if r else 'không dựng được'):<34}{dt:>7.0f}{dau}", flush=True)
