
import json
import os
import re
import sys
import urllib.request


API_BASE = os.environ.get("PIPELINE_API_BASE", "http://localhost:8000")

PROMPT = """You are solving a Lean 4 equational-theories problem over magmas.
The problem contains a hypothesis equation and a target equation.

Return exactly one JSON object and no Markdown.

For a true implication:
{"verdict":"true","proof":"<Lean tactic proof body only>"}

For a false implication:
{"verdict":"false","counterexample_table":[[0,1],[1,0]]}

Rules:
- The operation is an arbitrary binary operation. Do not assume associativity, commutativity, identity, or inverses.
- Keep Lean code minimal and compatible with the judge wrapper.
- Never use incomplete proof placeholders or unsafe mechanisms.
- If judge feedback is provided, revise the previous candidate instead of repeating it."""


def api_request(method: str, path: str, body: dict[str, object] | None = None) -> dict[str, object]:
    data = json.dumps(body).encode("utf-8") if body is not None else None
    request = urllib.request.Request(
        f"{API_BASE}{path}",
        data=data,
        method=method,
        headers={"Content-Type": "application/json"},
    )
    with urllib.request.urlopen(request, timeout=300) as response:
        payload = json.loads(response.read())
    data_payload = payload.get("data")
    if not isinstance(data_payload, dict):
        raise RuntimeError("API response is missing data object")
    return data_payload


def read_problem() -> dict[str, object]:
    raw_problem = os.environ.get("PROBLEM_JSON")
    if raw_problem:
        problem = json.loads(raw_problem)
    else:
        startup = json.loads(sys.stdin.readline())
        problem = startup.get("problem")
    if not isinstance(problem, dict):
        raise RuntimeError("Problem payload is missing")
    return problem


def create_session(problem: dict[str, object]) -> str:
    result = api_request("POST", "/api/stage2/pipeline/sessions", {"problem": problem})
    session_id = result.get("session_id")
    if not isinstance(session_id, str) or not session_id:
        raise RuntimeError("API response is missing session_id")
    return session_id


def close_session(session_id: str) -> None:
    api_request("DELETE", f"/api/stage2/pipeline/sessions/{session_id}")


def llm_chat(session_id: str, context: dict[str, object]) -> str:
    result = api_request("POST", f"/api/stage2/pipeline/sessions/{session_id}/llm", {"context": context})
    response = result.get("response")
    if not isinstance(response, str):
        raise RuntimeError("LLM response is missing")
    return response


def judge_answer(session_id: str, answer: dict[str, object]) -> dict[str, object]:
    verdict = answer.get("verdict")
    if verdict not in ("true", "false"):
        raise ValueError("answer verdict must be true or false")
    proof = answer.get("proof")
    code = proof if isinstance(proof, str) else answer.get("code")
    if verdict == "false" and isinstance(answer.get("counterexample_table"), list):
        code = json.dumps(answer["counterexample_table"])
    if not isinstance(code, str):
        raise ValueError("answer code is missing")
    return api_request("POST", f"/api/stage2/pipeline/sessions/{session_id}/judge", {"verdict": verdict, "code": code})


def parse_answer(response: str) -> dict[str, object] | None:
    stripped = response.strip()
    candidates = [stripped]
    candidates.extend(match.group(0) for match in re.finditer(r"\{[\s\S]*?\}", response))
    for candidate in candidates:
        try:
            parsed = json.loads(candidate)
        except json.JSONDecodeError:
            continue
        if isinstance(parsed, dict):
            return parsed
    return None


def compact_judge_feedback(result: dict[str, object]) -> dict[str, object]:
    return {
        "status": result.get("status"),
        "error_code": result.get("error_code"),
        "message": result.get("message"),
        "lean_stdout": result.get("lean_stdout"),
        "lean_stderr": result.get("lean_stderr"),
    }


def main() -> None:
    session_id = ""
    best_answer: dict[str, object] | None = None
    feedback: dict[str, object] | None = None
    try:
        problem = read_problem()
        session_id = create_session(problem)
        for round_index in range(8):
            context: dict[str, object] = {"round": round_index, "problem": problem}
            if feedback is not None:
                context["judge_feedback"] = feedback
            response = llm_chat(session_id, context)
            answer = parse_answer(response)
            if answer is None:
                feedback = {"status": "unparsed", "message": "Model did not return JSON"}
                continue
            best_answer = answer
            try:
                result = judge_answer(session_id, answer)
            except Exception as exc:
                feedback = {"status": "malformed", "message": str(exc), "answer": answer}
                continue
            if result.get("status") == "accepted":
                print(json.dumps({"solved": True, "verdict": answer.get("verdict"), "answer": answer, "judge": result}))
                return
            feedback = compact_judge_feedback(result)
        print(json.dumps({"solved": False, "answer": best_answer, "feedback": feedback}))
    except Exception as exc:
        print(json.dumps({"solved": False, "error": str(exc)}))
    finally:
        if session_id:
            try:
                close_session(session_id)
            except Exception:
                pass


if __name__ == "__main__":
    main()
