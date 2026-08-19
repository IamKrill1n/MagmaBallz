# Reja23 (EQT02-S00023) — Sơ đồ chiến lược

Sơ đồ hóa từ `SOLVER_STRATEGY.md` (Part 1). Hai sơ đồ: (1) vòng cộng tác LLM ↔ công cụ
cơ học, (2) vòng giải chính theo từng giai đoạn.

## 1. Ý tưởng cốt lõi — LLM điều hướng, công cụ cơ học chứng minh

```mermaid
flowchart LR
    subgraph LLM["LLM — chiến lược gia (không đáng tin)"]
        A["Nhận protocol state + blackboard,<br/>trả về đúng 1 JSON action"]
    end

    subgraph ACTIONS["Không gian hành động"]
        T1["tool_call<br/>(chọn công cụ + tham số)"]
        T2["midpoint / lemma_chain /<br/>candidate_bundle<br/>(bổ đề cầu nối)"]
        T3["false_model_family<br/>(họ phản mô hình có tham số)"]
        T4["symbolic_model_plan / patch<br/>(phản mô hình VÔ HẠN)"]
        T5["goal_proof / false_table<br/>(trực tiếp, hiếm)"]
    end

    subgraph MECH["Phía cơ học — đáng tin"]
        V["Kiểm chứng cơ học:<br/>H ⇒ M trước, rồi H + M ⇒ Goal"]
        REG["Registry công cụ:<br/>model finder, superposition,<br/>ordered completion, SAT/CP-SAT..."]
        BB[("Blackboard:<br/>bổ đề đã chứng minh /<br/>bác bỏ / hết ngân sách")]
    end

    A --> T1 & T2 & T3 & T4 & T5
    T1 --> REG
    T2 --> V
    T3 --> REG
    T4 --> V
    T5 --> V
    V -- "chứng minh được" --> BB
    V -- "không kiểm chứng được" --> DROP["Loại bỏ âm thầm"]
    REG -- "thất bại → protocol state JSON<br/>(status, contract, frontier, need_hint)" --> A
    BB -- "sống qua các vòng,<br/>bắc cầu về sau" --> A
```

Nguyên tắc: LLM **không bao giờ** viết chứng minh được nộp trực tiếp (trừ vài ngoại lệ
hẹp). Mọi gợi ý đều phải qua kiểm chứng cơ học; gợi ý hỏng bị vứt, thất bại của công cụ
được đóng gói thành telemetry (`sair-collab-protocol-v0`) nuôi vòng LLM kế tiếp.

## 2. Vòng giải chính — leo thang theo ngân sách

```mermaid
flowchart TD
    START(["Bài toán: H ⇒ Goal?"]) --> S1

    S1["Giai đoạn 1 — Kiểm toán ngữ nghĩa<br/>(implication_semantics)"]
    S1 -- "FALSE nhưng không thể có<br/>phản mô hình hữu hạn" --> INF["Đi thẳng LLM:<br/>symbolic_model_plan<br/>(phản mô hình vô hạn — kênh độc nhất)"]
    S1 -- "bình thường" --> S2

    S2["Giai đoạn 2 — Router cấu trúc<br/>(residue ray → checkpoint LLM sớm)"] --> S3

    S3["Giai đoạn 3 — Rigidity scout<br/>(liệt kê mô hình của H đến cỡ 4)"]
    S3 -- "không có mô hình không tầm thường<br/>→ tín hiệu H sụp đổ (chỉ để định tuyến)" --> COLL["rigidity_collapse_portfolio_attempt<br/>(danh mục chứng minh sụp đổ)"]
    S3 -- "có mô hình" --> S4
    COLL -- "thất bại" --> S4

    S4["Giai đoạn 4 — FALSE rẻ<br/>small_false_search, model_finder_v2 (n=4,5),<br/>skew product (n=6)"] --> S5

    S5["Giai đoạn 5 — TRUE rẻ<br/>superposition + bổ đề chuẩn (có retry theo phản hồi),<br/>derived proofs, helper-chain, ứng viên cú pháp"] --> S6

    S6["Giai đoạn 6 — Cộng tác LLM xen kẽ<br/>(goal viết riêng mỗi lượt, mang telemetry,<br/>chống lặp bằng failure signature)"] --> S7

    S7["Giai đoạn 7 — FALSE nặng<br/>model_finder_v2 (n=6..8), promoted exact continuation,<br/>stochastic local search, SAT (sympy), CP-SAT,<br/>poly_ce (đến n=13), họ cấu trúc (đến n=7)"] --> S8

    S8["Giai đoạn 8 — TRUE nặng<br/>pc_saturate (bão hòa paramodulation, xuất Lean),<br/>ordered completion kiểu Knuth–Bendix (discover + replay)"] --> S9

    S9["Giai đoạn 9 — Cứu vãn<br/>2 lượt LLM cuối: nhận toàn bộ frontier + thất bại,<br/>yêu cầu SỬA hành động cũ, không làm lại"]

    INF --> SUBMIT
    S9 --> SUBMIT(["Nộp chứng chỉ Lean cho giám khảo<br/>(bị từ chối → coi là phản hồi, thử tiếp)"])
```

## 3. Đối chiếu một dòng

| | reja23 | EQT02-M00006 (ta) |
|---|---|---|
| Triết lý | Độ rộng + LLM điều hướng | Bậc thang tất định, kiểm chứng trước khi nộp |
| Điểm số (800) | 762 | 786 |
| Nộp bị bác bỏ | 252 | 0 |
| Phụ thuộc LLM | Cấu trúc (routing, cầu nối) | Không (786/800 khi tắt LLM) |
