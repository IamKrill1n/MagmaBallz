"""Deterministic, zero-LLM Solo solver for magma-law implications.

The file is deliberately self-contained: the submission contract mounts only
``solver.py``.  Its sections implement the kernel, disabled oracle seam,
strategy registry, case engine, and line-delimited protocol adapter.
"""

from __future__ import annotations

import hashlib
import itertools
import json
import re
import sys
import time
from collections import deque
from dataclasses import dataclass, field, replace
from typing import Callable, Iterable, Iterator, Mapping, Protocol, Sequence


PROMPT = ""

LANE_COUNTERMODEL = "countermodel"
LANE_PROOF = "proof"
ORACLE_MODE = "disabled"
ORACLE_ARTIFACT = b""
TRACE_PREFIX = "MAGMABALLZ_TRACE "


# ---------------------------------------------------------------------------
# Solver kernel


@dataclass(frozen=True, slots=True)
class Var:
    scope: str
    slot: int
    display_name: str = field(compare=False, hash=False)


@dataclass(frozen=True, slots=True)
class App:
    left: "Term"
    right: "Term"


Term = Var | App


@dataclass(frozen=True, slots=True)
class Equation:
    variables: tuple[Var, ...]
    lhs: Term
    rhs: Term

    def __post_init__(self) -> None:
        expected = {(variable.scope, variable.slot) for variable in self.variables}
        actual = {(variable.scope, variable.slot) for variable in term_variables(self.lhs)}
        actual.update(
            (variable.scope, variable.slot) for variable in term_variables(self.rhs)
        )
        if actual != expected:
            raise ValueError("equation variables do not match its terms")


@dataclass(frozen=True, slots=True)
class Problem:
    premise: Equation
    goal: Equation
    fingerprint: str


@dataclass(frozen=True, slots=True)
class FiniteMagma:
    order: int
    cells: tuple[int, ...]

    def __post_init__(self) -> None:
        if type(self.order) is not int or self.order <= 0:
            raise ValueError("magma order must be a positive integer")
        if len(self.cells) != self.order * self.order:
            raise ValueError("magma table is not square")
        if any(type(value) is not int or not 0 <= value < self.order for value in self.cells):
            raise ValueError("magma cell is outside the carrier")


@dataclass(frozen=True, slots=True)
class Derivation:
    rule: str
    left: Term
    right: Term
    substitution: tuple[Term, ...] = ()
    children: tuple["Derivation", ...] = ()


@dataclass(frozen=True, slots=True)
class Provenance:
    strategy_id: str
    strategy_version: str
    candidate_index: int
    cumulative_credits: int
    evidence_fingerprint: str = ""


@dataclass(frozen=True, slots=True)
class Candidate:
    kind: str
    payload: Derivation | FiniteMagma | str
    provenance: Provenance | None = None


@dataclass(frozen=True, slots=True)
class EffortBudget:
    credits: int
    hard_deadline: float


@dataclass(frozen=True, slots=True)
class AdvanceResult:
    status: str
    candidate: Candidate | None = None
    credits_used: int = 0
    fault: str | None = None


@dataclass(frozen=True, slots=True)
class Limits:
    max_code_length: int
    max_false_cert_bytes: int


@dataclass(slots=True)
class SeenCandidates:
    evidence: set[str] = field(default_factory=set)
    requests: set[str] = field(default_factory=set)


@dataclass(frozen=True, slots=True)
class Admission:
    status: str
    reason: str
    evidence_fingerprint: str
    verdict: str | None = None
    source: str | None = None
    request_fingerprint: str | None = None


def _digest(value: object, *, size: int = 16) -> str:
    encoded = json.dumps(
        value, ensure_ascii=False, separators=(",", ":"), sort_keys=True
    ).encode("utf-8")
    return hashlib.blake2s(encoded, digest_size=size).hexdigest()


def term_key(term: Term) -> tuple[object, ...]:
    if isinstance(term, Var):
        return ("v", term.scope, term.slot)
    return ("a", term_key(term.left), term_key(term.right))


def term_size(term: Term) -> int:
    if isinstance(term, Var):
        return 1
    return 1 + term_size(term.left) + term_size(term.right)


def term_variables(term: Term) -> Iterator[Var]:
    if isinstance(term, Var):
        yield term
        return
    yield from term_variables(term.left)
    yield from term_variables(term.right)


def subterms(term: Term) -> Iterator[Term]:
    yield term
    if isinstance(term, App):
        yield from subterms(term.left)
        yield from subterms(term.right)


def term_to_lean(term: Term) -> str:
    if isinstance(term, Var):
        if term.scope != "goal":
            raise ValueError("only goal-scoped terms may be rendered directly")
        return f"v{term.slot}"
    return f"({term_to_lean(term.left)} ◇ {term_to_lean(term.right)})"


def _strip_outer_parentheses(text: str) -> str:
    text = text.strip()
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        closes_at_end = True
        for index, character in enumerate(text):
            if character == "(":
                depth += 1
            elif character == ")":
                depth -= 1
                if depth < 0:
                    raise ValueError("unbalanced term parentheses")
            if depth == 0 and index != len(text) - 1:
                closes_at_end = False
                break
        if depth != 0:
            raise ValueError("unbalanced term parentheses")
        if not closes_at_end:
            break
        text = text[1:-1].strip()
    return text


def _parse_term(text: str, variables: Mapping[str, Var]) -> Term:
    text = _strip_outer_parentheses(text.replace("*", "◇"))
    depth = 0
    split_at = -1
    for index, character in enumerate(text):
        if character == "(":
            depth += 1
        elif character == ")":
            depth -= 1
            if depth < 0:
                raise ValueError("unbalanced term parentheses")
        elif character == "◇" and depth == 0:
            split_at = index
    if depth != 0:
        raise ValueError("unbalanced term parentheses")
    if split_at >= 0:
        return App(
            _parse_term(text[:split_at], variables),
            _parse_term(text[split_at + 1 :], variables),
        )
    name = text.strip()
    if name not in variables:
        raise ValueError(f"invalid variable term: {name!r}")
    return variables[name]


def parse_equation(text: str, scope: str) -> Equation:
    if not isinstance(text, str) or text.count("=") != 1:
        raise ValueError("equation must contain exactly one equality")
    normalized = text.replace("*", "◇")
    if not re.fullmatch(r"[\sa-z◇=()]+", normalized):
        raise ValueError("equation contains unsupported characters")
    names = tuple(dict.fromkeys(re.findall(r"\b([a-z])\b", normalized)))
    if not names:
        raise ValueError("equation has no variables")
    variables = tuple(Var(scope, slot, name) for slot, name in enumerate(names))
    by_name = {variable.display_name: variable for variable in variables}
    lhs_text, rhs_text = normalized.split("=", 1)
    return Equation(
        variables,
        _parse_term(lhs_text, by_name),
        _parse_term(rhs_text, by_name),
    )


def parse_problem(public_problem: Mapping[str, object]) -> Problem:
    if not isinstance(public_problem, Mapping):
        raise ValueError("public problem must be an object")
    premise = parse_equation(str(public_problem["equation1"]), "premise")
    goal = parse_equation(str(public_problem["equation2"]), "goal")
    fingerprint = _digest(
        {
            "canonicalization": 1,
            "premise": [term_key(premise.lhs), term_key(premise.rhs)],
            "goal": [term_key(goal.lhs), term_key(goal.rhs)],
        }
    )
    return Problem(premise, goal, fingerprint)


def substitute(term: Term, substitution: Sequence[Term]) -> Term:
    if isinstance(term, Var):
        if term.scope != "premise" or not 0 <= term.slot < len(substitution):
            raise ValueError("substitution does not cover a premise variable")
        return substitution[term.slot]
    return App(
        substitute(term.left, substitution),
        substitute(term.right, substitution),
    )


def match_term(
    pattern: Term, target: Term, mapping: Mapping[int, Term] | None = None
) -> dict[int, Term] | None:
    result = dict(mapping or {})
    if isinstance(pattern, Var):
        if pattern.scope != "premise":
            return None
        current = result.get(pattern.slot)
        if current is None:
            result[pattern.slot] = target
            return result
        return result if current == target else None
    if not isinstance(target, App):
        return None
    result = match_term(pattern.left, target.left, result)
    if result is None:
        return None
    return match_term(pattern.right, target.right, result)


def refl(term: Term) -> Derivation:
    return Derivation("refl", term, term)


def hypothesis(problem: Problem, substitution: Sequence[Term]) -> Derivation:
    values = tuple(substitution)
    if len(values) != len(problem.premise.variables):
        raise ValueError("premise substitution is not total")
    if any(variable.scope != "goal" for term in values for variable in term_variables(term)):
        raise ValueError("premise substitution contains a foreign variable")
    return Derivation(
        "hyp",
        substitute(problem.premise.lhs, values),
        substitute(problem.premise.rhs, values),
        substitution=values,
    )


def symmetry(proof: Derivation) -> Derivation:
    return Derivation("symm", proof.right, proof.left, children=(proof,))


def transitivity(first: Derivation, second: Derivation) -> Derivation:
    if first.right != second.left:
        raise ValueError("transitivity proofs have different middle terms")
    return Derivation(
        "trans", first.left, second.right, children=(first, second)
    )


def congruence(left: Derivation, right: Derivation) -> Derivation:
    return Derivation(
        "congr",
        App(left.left, right.left),
        App(left.right, right.right),
        children=(left, right),
    )


def _replay_derivation(
    problem: Problem,
    proof: Derivation,
    active: set[int],
    memo: dict[int, tuple[Term, Term, object]],
) -> tuple[Term, Term, object]:
    identity = id(proof)
    if identity in memo:
        return memo[identity]
    if identity in active:
        raise ValueError("cyclic derivation")
    active.add(identity)
    if proof.rule == "refl" and not proof.children and not proof.substitution:
        computed = (proof.left, proof.left, ("refl", term_key(proof.left)))
    elif proof.rule == "hyp" and not proof.children:
        rebuilt = hypothesis(problem, proof.substitution)
        computed = (
            rebuilt.left,
            rebuilt.right,
            ("hyp", tuple(term_key(term) for term in proof.substitution)),
        )
    elif proof.rule == "symm" and len(proof.children) == 1:
        left, right, child_key = _replay_derivation(
            problem, proof.children[0], active, memo
        )
        computed = (right, left, ("symm", child_key))
    elif proof.rule == "trans" and len(proof.children) == 2:
        left1, right1, key1 = _replay_derivation(
            problem, proof.children[0], active, memo
        )
        left2, right2, key2 = _replay_derivation(
            problem, proof.children[1], active, memo
        )
        if right1 != left2:
            raise ValueError("invalid transitivity midpoint")
        computed = (left1, right2, ("trans", key1, key2))
    elif proof.rule == "congr" and len(proof.children) == 2:
        left1, right1, key1 = _replay_derivation(
            problem, proof.children[0], active, memo
        )
        left2, right2, key2 = _replay_derivation(
            problem, proof.children[1], active, memo
        )
        computed = (App(left1, left2), App(right1, right2), ("congr", key1, key2))
    else:
        raise ValueError("unsupported or malformed derivation rule")
    active.remove(identity)
    if (proof.left, proof.right) != computed[:2]:
        raise ValueError("stored derivation endpoints do not replay")
    memo[identity] = computed
    return computed


def replay_derivation(problem: Problem, proof: Derivation) -> object:
    left, right, key = _replay_derivation(problem, proof, set(), {})
    if left != problem.goal.lhs or right != problem.goal.rhs:
        raise ValueError("derivation does not prove the goal")
    return key


def evaluate(term: Term, assignment: Sequence[int], magma: FiniteMagma) -> int:
    if isinstance(term, Var):
        return assignment[term.slot]
    left = evaluate(term.left, assignment, magma)
    right = evaluate(term.right, assignment, magma)
    return magma.cells[left * magma.order + right]


def equation_holds(equation: Equation, magma: FiniteMagma) -> bool:
    assignments = itertools.product(
        range(magma.order), repeat=len(equation.variables)
    )
    return all(
        evaluate(equation.lhs, assignment, magma)
        == evaluate(equation.rhs, assignment, magma)
        for assignment in assignments
    )


def validate_countermodel(
    problem: Problem, magma: FiniteMagma
) -> tuple[int, ...]:
    if not equation_holds(problem.premise, magma):
        raise ValueError("magma does not satisfy the premise")
    for assignment in itertools.product(
        range(magma.order), repeat=len(problem.goal.variables)
    ):
        if evaluate(problem.goal.lhs, assignment, magma) != evaluate(
            problem.goal.rhs, assignment, magma
        ):
            return tuple(assignment)
    raise ValueError("magma also satisfies the goal")


def _render_derivation(proof: Derivation) -> str:
    if proof.rule == "refl":
        return "rfl"
    if proof.rule == "hyp":
        arguments = " ".join(term_to_lean(term) for term in proof.substitution)
        return f"h {arguments}" if arguments else "h"
    if proof.rule == "symm":
        return f"({_render_derivation(proof.children[0])}).symm"
    if proof.rule == "trans":
        first, second = proof.children
        return (
            f"({_render_derivation(first)}).trans "
            f"({_render_derivation(second)})"
        )
    if proof.rule == "congr":
        left, right = proof.children
        left_step = (
            "congrArg (fun t : G => t ◇ "
            f"{term_to_lean(right.left)}) "
            f"({_render_derivation(left)})"
        )
        right_step = (
            "congrArg (fun t : G => "
            f"{term_to_lean(left.right)} ◇ t) ({_render_derivation(right)})"
        )
        return f"({left_step}).trans ({right_step})"
    raise ValueError("cannot render derivation rule")


def render_true(problem: Problem, proof: Derivation) -> str:
    binders = " ".join(f"v{index}" for index in range(len(problem.goal.variables)))
    binder_line = f"  intro {binders}\n" if binders else ""
    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        f"{binder_line}"
        f"  exact {_render_derivation(proof)}\n"
    )


def render_false(magma: FiniteMagma) -> str:
    rows = [
        list(magma.cells[row * magma.order : (row + 1) * magma.order])
        for row in range(magma.order)
    ]
    table = json.dumps(rows, separators=(",", ":"))
    return (
        "import JudgeProblem\n"
        "import JudgeDecide.DecideBang\n"
        "import JudgeFinOp.MemoFinOp\n"
        "open MemoFinOp\n\n"
        "def submission : Goal := by\n"
        f"  let m : Magma (Fin {magma.order}) := {{\n"
        f"    op := finOpTable \"{table}\"\n"
        "  }\n"
        f"  refine ⟨Fin {magma.order}, m, ?_⟩\n"
        "  decideFin!\n"
    )


_BANNED_TOKENS = (
    "sorry",
    "admit",
    "sorryAx",
    "mkSorry",
    "dbg_trace",
    "dbgTrace",
    "run_tac",
    "initialize",
    "builtin_initialize",
    "#eval",
    "#exit",
    "#reduce",
    "#synth",
    "#check_eval",
    "elab",
    "elab_rules",
    "macro",
    "macro_rules",
    "syntax",
    "unsafe",
    "implemented_by",
    "extern",
    "unsafeCast",
    "unsafeIO",
    "unsafePerformIO",
)


def _banned_token(source: str) -> str | None:
    for token in _BANNED_TOKENS:
        pattern = re.escape(token) if token.startswith("#") else rf"\b{re.escape(token)}\b"
        if re.search(pattern, source):
            return token
    return None


def _normalize_lean_body(body: str) -> str:
    return body.replace("\r\n", "\n").replace("\r", "\n").strip("\n")


def _render_lean_body(problem: Problem, body: str) -> str:
    binders = " ".join(f"v{index}" for index in range(len(problem.goal.variables)))
    lines = ["import JudgeProblem", "", "def submission : Goal := by", "  intro G _ h"]
    if binders:
        lines.append(f"  intro {binders}")
    lines.extend("  " + line if line.strip() else "" for line in body.splitlines())
    return "\n".join(lines) + "\n"


def _payload_fingerprint(
    problem: Problem, candidate: Candidate
) -> tuple[str, object, bool]:
    if candidate.kind == "derivation" and isinstance(candidate.payload, Derivation):
        return "derivation", replay_derivation(problem, candidate.payload), True
    if candidate.kind == "countermodel" and isinstance(candidate.payload, FiniteMagma):
        return "countermodel", (candidate.payload.order, candidate.payload.cells), False
    if candidate.kind == "lean_body" and isinstance(candidate.payload, str):
        return "lean_body", _normalize_lean_body(candidate.payload), False
    raise ValueError("candidate kind and payload disagree")


def admit(
    problem: Problem,
    candidate: Candidate,
    limits: Limits,
    seen: SeenCandidates,
) -> Admission:
    try:
        kind, payload_key, already_validated = _payload_fingerprint(problem, candidate)
    except (TypeError, ValueError) as error:
        fingerprint = _digest(
            ("malformed", candidate.kind, type(candidate.payload).__name__, str(error))
        )
        if fingerprint in seen.evidence:
            return Admission("duplicate", "evidence_duplicate", fingerprint)
        seen.evidence.add(fingerprint)
        return Admission("rejected", str(error), fingerprint)
    fingerprint = _digest((problem.fingerprint, kind, payload_key))
    if fingerprint in seen.evidence:
        return Admission("duplicate", "evidence_duplicate", fingerprint)
    seen.evidence.add(fingerprint)

    try:
        if kind == "derivation":
            proof = candidate.payload
            assert isinstance(proof, Derivation)
            if not already_validated:
                replay_derivation(problem, proof)
            source = render_true(problem, proof)
            verdict = "true"
        elif kind == "countermodel":
            magma = candidate.payload
            assert isinstance(magma, FiniteMagma)
            validate_countermodel(problem, magma)
            source = render_false(magma)
            verdict = "false"
        else:
            body = candidate.payload
            assert isinstance(body, str)
            body = _normalize_lean_body(body)
            if not body.strip():
                raise ValueError("Lean body is empty")
            if re.search(
                r"(?m)^\s*(import|namespace|section|theorem|def|axiom|example|inductive|structure)\b",
                body,
            ):
                raise ValueError("Lean body contains top-level scaffolding")
            source = _render_lean_body(problem, body)
            verdict = "true"
        banned = _banned_token(source)
        if banned is not None:
            raise ValueError(f"source contains banned token: {banned}")
        source_bytes = source.encode("utf-8")
        if len(source_bytes) > limits.max_code_length:
            raise ValueError("rendered source exceeds the code limit")
        if verdict == "false" and len(source_bytes) > limits.max_false_cert_bytes:
            raise ValueError("countermodel source exceeds the false-certificate limit")
    except (AssertionError, TypeError, ValueError) as error:
        return Admission("rejected", str(error), fingerprint)

    request_fingerprint = _digest(
        (problem.fingerprint, verdict, source), size=20
    )
    if request_fingerprint in seen.requests:
        return Admission(
            "duplicate",
            "request_duplicate",
            fingerprint,
            request_fingerprint=request_fingerprint,
        )
    seen.requests.add(request_fingerprint)
    return Admission(
        "judge_request",
        "locally_admissible",
        fingerprint,
        verdict,
        source,
        request_fingerprint,
    )


# ---------------------------------------------------------------------------
# Oracle subsystem


@dataclass(frozen=True, slots=True)
class OracleResult:
    cached_candidate: Candidate | None
    preferred_lane: str | None
    disposition: str
    artifact_ref: str | None = None


class OracleSubsystem:
    def __init__(self, mode: str, artifact_bytes: object):
        if mode not in ("disabled", "enabled"):
            raise ValueError("oracle mode must be disabled or enabled")
        self.mode = mode
        self._artifact_bytes = artifact_bytes

    def consult(
        self,
        problem: Problem,
        eq1_id: object,
        eq2_id: object,
    ) -> OracleResult:
        del problem, eq1_id, eq2_id
        if self.mode == "disabled":
            return OracleResult(None, None, "disabled")
        if not isinstance(self._artifact_bytes, bytes) or not self._artifact_bytes:
            return OracleResult(None, None, "miss")
        return OracleResult(None, None, "invalid")


# ---------------------------------------------------------------------------
# Strategy implementations and stable registry


class StrategySession(Protocol):
    def advance(self, budget: EffortBudget) -> AdvanceResult: ...


@dataclass(frozen=True, slots=True)
class Strategy:
    id: str
    version: str
    lane: str
    opener: Callable[[Problem], StrategySession] = field(compare=False, repr=False)

    def open(self, problem: Problem) -> StrategySession:
        return self.opener(problem)


class _GeneratorSession:
    def __init__(self, events: Iterator[Candidate | None], work_per_credit: int):
        self._events = events
        self._work_per_credit = work_per_credit
        self._terminal = False

    def advance(self, budget: EffortBudget) -> AdvanceResult:
        if self._terminal:
            return AdvanceResult("exhausted")
        completed = 0
        allowance = max(1, budget.credits * self._work_per_credit)
        try:
            while completed < allowance:
                if time.monotonic() >= budget.hard_deadline:
                    return AdvanceResult(
                        "paused", credits_used=1 if completed else 0
                    )
                event = next(self._events)
                completed += 1
                if event is not None:
                    return AdvanceResult("yielded", event, 1)
        except StopIteration:
            self._terminal = True
            return AdvanceResult("exhausted", credits_used=1 if completed else 0)
        except Exception as error:  # A strategy fault must not stop other lanes.
            self._terminal = True
            return AdvanceResult(
                "fault",
                credits_used=1 if completed else 0,
                fault=f"{type(error).__name__}: {error}",
            )
        return AdvanceResult("paused", credits_used=budget.credits)


def _complete_substitution(
    problem: Problem, mapping: Mapping[int, Term], default: Term
) -> tuple[Term, ...]:
    return tuple(
        mapping.get(variable.slot, default) for variable in problem.premise.variables
    )


@dataclass(frozen=True, slots=True)
class _Meta:
    copy: int
    slot: int


@dataclass(frozen=True, slots=True)
class _UApp:
    left: "_UTerm"
    right: "_UTerm"


_UTerm = _Meta | Var | _UApp


def _to_unification_term(term: Term, copy: int | None) -> _UTerm:
    if isinstance(term, Var):
        if copy is not None and term.scope == "premise":
            return _Meta(copy, term.slot)
        return term
    return _UApp(
        _to_unification_term(term.left, copy),
        _to_unification_term(term.right, copy),
    )


def _resolve_meta(term: _UTerm, mapping: dict[_Meta, _UTerm]) -> _UTerm:
    trail: set[_Meta] = set()
    while isinstance(term, _Meta) and term in mapping:
        if term in trail:
            raise ValueError("cyclic unification substitution")
        trail.add(term)
        term = mapping[term]
    return term


def _occurs(meta: _Meta, term: _UTerm, mapping: dict[_Meta, _UTerm]) -> bool:
    term = _resolve_meta(term, mapping)
    if isinstance(term, _Meta):
        return term == meta
    if isinstance(term, _UApp):
        return _occurs(meta, term.left, mapping) or _occurs(meta, term.right, mapping)
    return False


def _unify(left: _UTerm, right: _UTerm, mapping: dict[_Meta, _UTerm]) -> bool:
    left = _resolve_meta(left, mapping)
    right = _resolve_meta(right, mapping)
    if left == right:
        return True
    if isinstance(left, _Meta):
        if _occurs(left, right, mapping):
            return False
        mapping[left] = right
        return True
    if isinstance(right, _Meta):
        return _unify(right, left, mapping)
    if isinstance(left, _UApp) and isinstance(right, _UApp):
        return _unify(left.left, right.left, mapping) and _unify(
            left.right, right.right, mapping
        )
    return False


def _materialize(term: _UTerm, mapping: dict[_Meta, _UTerm]) -> Term:
    term = _resolve_meta(term, mapping)
    if isinstance(term, _Meta):
        raise ValueError("unification left an unbound premise variable")
    if isinstance(term, Var):
        if term.scope != "goal":
            raise ValueError("unification produced a foreign variable")
        return term
    return App(_materialize(term.left, mapping), _materialize(term.right, mapping))


def _oriented_hypothesis(
    problem: Problem, substitution: Sequence[Term], reverse: bool
) -> Derivation:
    proof = hypothesis(problem, substitution)
    return symmetry(proof) if reverse else proof


def _chain_derivations(problem: Problem) -> Iterator[Derivation]:
    default = problem.goal.variables[0]
    premise_sides = (problem.premise.lhs, problem.premise.rhs)
    goal_sides = (problem.goal.lhs, problem.goal.rhs)

    for reverse in (False, True):
        source, target = (
            (premise_sides[1], premise_sides[0])
            if reverse
            else premise_sides
        )
        mapping: dict[_Meta, _UTerm] = {}
        if not _unify(
            _to_unification_term(source, 0),
            _to_unification_term(goal_sides[0], None),
            mapping,
        ) or not _unify(
            _to_unification_term(target, 0),
            _to_unification_term(goal_sides[1], None),
            mapping,
        ):
            continue
        for variable in problem.premise.variables:
            mapping.setdefault(_Meta(0, variable.slot), _to_unification_term(default, None))
        substitution = tuple(
            _materialize(_Meta(0, variable.slot), mapping)
            for variable in problem.premise.variables
        )
        yield _oriented_hypothesis(problem, substitution, reverse)

    for first_reverse in (False, True):
        for second_reverse in (False, True):
            first_source, first_mid = (
                (premise_sides[1], premise_sides[0])
                if first_reverse
                else premise_sides
            )
            second_mid, second_target = (
                (premise_sides[1], premise_sides[0])
                if second_reverse
                else premise_sides
            )
            mapping = {}
            constraints = (
                (
                    _to_unification_term(first_source, 0),
                    _to_unification_term(goal_sides[0], None),
                ),
                (
                    _to_unification_term(second_target, 1),
                    _to_unification_term(goal_sides[1], None),
                ),
                (
                    _to_unification_term(first_mid, 0),
                    _to_unification_term(second_mid, 1),
                ),
            )
            if not all(_unify(left, right, mapping) for left, right in constraints):
                continue
            for copy in (0, 1):
                for variable in problem.premise.variables:
                    mapping.setdefault(
                        _Meta(copy, variable.slot),
                        _to_unification_term(default, None),
                    )
            substitutions = [
                tuple(
                    _materialize(_Meta(copy, variable.slot), mapping)
                    for variable in problem.premise.variables
                )
                for copy in (0, 1)
            ]
            first = _oriented_hypothesis(problem, substitutions[0], first_reverse)
            second = _oriented_hypothesis(problem, substitutions[1], second_reverse)
            yield transitivity(first, second)


def _one_sided_variables(problem: Problem) -> Iterator[tuple[int, bool, Term]]:
    left_slots = {variable.slot for variable in term_variables(problem.premise.lhs)}
    right_slots = {variable.slot for variable in term_variables(problem.premise.rhs)}
    for variable in problem.premise.variables:
        if variable.slot in left_slots - right_slots:
            yield variable.slot, True, problem.premise.lhs
        elif variable.slot in right_slots - left_slots:
            yield variable.slot, False, problem.premise.rhs


def _constancy_between(problem: Problem, left: Term, right: Term) -> Derivation | None:
    default = problem.goal.variables[0]
    for varying_slot, variable_on_left, varying_side in _one_sided_variables(problem):
        first_map = match_term(varying_side, left)
        second_map = match_term(varying_side, right)
        if first_map is None or second_map is None:
            continue
        comparable = [
            variable.slot
            for variable in problem.premise.variables
            if variable.slot != varying_slot
        ]
        if any(first_map.get(slot, default) != second_map.get(slot, default) for slot in comparable):
            continue
        first_sub = _complete_substitution(problem, first_map, default)
        second_sub = _complete_substitution(problem, second_map, default)
        first = hypothesis(problem, first_sub)
        second = hypothesis(problem, second_sub)
        try:
            if variable_on_left:
                return transitivity(first, symmetry(second))
            return transitivity(symmetry(first), second)
        except ValueError:
            continue
    return None


def _lift_matching_context(
    problem: Problem,
    left: Term,
    right: Term,
    leaf: Callable[[Problem, Term, Term], Derivation | None],
    depth: int = 0,
) -> Derivation | None:
    direct = leaf(problem, left, right)
    if direct is not None:
        return direct
    if depth >= 4 or not isinstance(left, App) or not isinstance(right, App):
        return None
    if left.right == right.right:
        child = _lift_matching_context(
            problem, left.left, right.left, leaf, depth + 1
        )
        if child is not None:
            return congruence(child, refl(left.right))
    if left.left == right.left:
        child = _lift_matching_context(
            problem, left.right, right.right, leaf, depth + 1
        )
        if child is not None:
            return congruence(refl(left.left), child)
    return None


def _direct_between(problem: Problem, left: Term, right: Term) -> Derivation | None:
    default = problem.goal.variables[0]
    for reverse, source, target in (
        (False, problem.premise.lhs, problem.premise.rhs),
        (True, problem.premise.rhs, problem.premise.lhs),
    ):
        mapping = match_term(source, left)
        if mapping is None:
            continue
        mapping = match_term(target, right, mapping)
        if mapping is None:
            continue
        substitution = _complete_substitution(problem, mapping, default)
        proof = _oriented_hypothesis(problem, substitution, reverse)
        if proof.left == left and proof.right == right:
            return proof
    return None


def _closed_form_events(problem: Problem) -> Iterator[Candidate | None]:
    if problem.goal.lhs == problem.goal.rhs:
        yield Candidate("derivation", refl(problem.goal.lhs))
    default = problem.goal.variables[0]
    for variable_on_left, bare, other in (
        (True, problem.premise.lhs, problem.premise.rhs),
        (False, problem.premise.rhs, problem.premise.lhs),
    ):
        if not isinstance(bare, Var):
            continue
        if any(variable.slot == bare.slot for variable in term_variables(other)):
            continue
        first = [default] * len(problem.premise.variables)
        second = list(first)
        first[bare.slot] = problem.goal.lhs
        second[bare.slot] = problem.goal.rhs
        first_proof = hypothesis(problem, first)
        second_proof = hypothesis(problem, second)
        proof = (
            transitivity(first_proof, symmetry(second_proof))
            if variable_on_left
            else transitivity(symmetry(first_proof), second_proof)
        )
        yield Candidate("derivation", proof)
    constancy = _lift_matching_context(
        problem, problem.goal.lhs, problem.goal.rhs, _constancy_between
    )
    if constancy is not None:
        yield Candidate("derivation", constancy)


def _short_chain_events(problem: Problem) -> Iterator[Candidate | None]:
    for proof in _chain_derivations(problem):
        yield Candidate("derivation", proof)


def _specialized_events(problem: Problem) -> Iterator[Candidate | None]:
    direct = _lift_matching_context(
        problem, problem.goal.lhs, problem.goal.rhs, _direct_between
    )
    if direct is not None:
        yield Candidate("derivation", direct)
    constancy = _lift_matching_context(
        problem, problem.goal.lhs, problem.goal.rhs, _constancy_between
    )
    if constancy is not None:
        yield Candidate("derivation", constancy)

    # Compound-pivot and collapse/spine synthesis.  Each first step is a
    # completely instantiated premise rewrite (possibly below the root); the
    # bridge is either another instantiated rewrite or a fully retained
    # one-sided-variable constancy derivation.
    pool = _term_pool(problem)
    for index, (middle, first) in enumerate(
        _rewrite_edges(problem, problem.goal.lhs, pool)
    ):
        if index >= 256:
            break
        bridge = _lift_matching_context(
            problem, middle, problem.goal.rhs, _direct_between
        ) or _lift_matching_context(
            problem, middle, problem.goal.rhs, _constancy_between
        )
        if bridge is not None:
            try:
                yield Candidate("derivation", transitivity(first, bridge))
            except ValueError:
                pass
        yield None

    for index, (middle, from_right) in enumerate(
        _rewrite_edges(problem, problem.goal.rhs, pool)
    ):
        if index >= 128:
            break
        bridge = _lift_matching_context(
            problem, problem.goal.lhs, middle, _direct_between
        ) or _lift_matching_context(
            problem, problem.goal.lhs, middle, _constancy_between
        )
        if bridge is not None:
            try:
                yield Candidate(
                    "derivation", transitivity(bridge, symmetry(from_right))
                )
            except ValueError:
                pass
        yield None


def _term_pool(problem: Problem) -> tuple[Term, ...]:
    terms: list[Term] = list(problem.goal.variables)
    for root in (problem.goal.lhs, problem.goal.rhs):
        terms.extend(term for term in subterms(root) if term_size(term) <= 9)
    terms.extend(App(left, right) for left in problem.goal.variables for right in problem.goal.variables)
    unique = {term_key(term): term for term in terms}
    ordered = sorted(unique.values(), key=lambda term: (term_size(term), term_key(term)))
    return tuple(ordered[:32])


def _all_paths(term: Term, path: tuple[int, ...] = ()) -> Iterator[tuple[tuple[int, ...], Term]]:
    yield path, term
    if isinstance(term, App):
        yield from _all_paths(term.left, path + (0,))
        yield from _all_paths(term.right, path + (1,))


def _replace_and_lift(
    root: Term,
    path: tuple[int, ...],
    replacement: Term,
    inner: Derivation,
) -> tuple[Term, Derivation]:
    if not path:
        return replacement, inner
    if not isinstance(root, App):
        raise ValueError("rewrite path left the term tree")
    if path[0] == 0:
        changed, child = _replace_and_lift(root.left, path[1:], replacement, inner)
        return App(changed, root.right), congruence(child, refl(root.right))
    changed, child = _replace_and_lift(root.right, path[1:], replacement, inner)
    return App(root.left, changed), congruence(refl(root.left), child)


def _rewrite_edges(
    problem: Problem, root: Term, pool: Sequence[Term]
) -> Iterator[tuple[Term, Derivation]]:
    for path, current in _all_paths(root):
        for reverse, source, target in (
            (False, problem.premise.lhs, problem.premise.rhs),
            (True, problem.premise.rhs, problem.premise.lhs),
        ):
            partial = match_term(source, current)
            if partial is None:
                continue
            missing = [
                variable.slot
                for variable in problem.premise.variables
                if variable.slot not in partial
            ]
            completion_pool: Sequence[Term] = pool
            if len(missing) >= 3:
                completion_pool = problem.goal.variables
            if len(missing) > 3:
                continue
            combinations: Iterable[tuple[Term, ...]] = itertools.product(
                completion_pool, repeat=len(missing)
            )
            for index, combination in enumerate(combinations):
                if index >= 96:
                    break
                mapping = dict(partial)
                mapping.update(zip(missing, combination))
                substitution = _complete_substitution(problem, mapping, pool[0])
                changed = substitute(target, substitution)
                if changed == current:
                    continue
                inner = _oriented_hypothesis(problem, substitution, reverse)
                new_root, edge = _replace_and_lift(root, path, changed, inner)
                yield new_root, edge
        for changed in pool:
            if changed == current:
                continue
            inner = _constancy_between(problem, current, changed)
            if inner is None:
                continue
            new_root, edge = _replace_and_lift(root, path, changed, inner)
            yield new_root, edge


def _rewrite_events(problem: Problem) -> Iterator[Candidate | None]:
    pool = _term_pool(problem)
    forward: dict[Term, Derivation] = {
        problem.goal.lhs: refl(problem.goal.lhs)
    }
    backward: dict[Term, Derivation] = {
        problem.goal.rhs: refl(problem.goal.rhs)
    }
    queues = (
        deque([(problem.goal.lhs, 0)]),
        deque([(problem.goal.rhs, 0)]),
    )
    stores = (forward, backward)
    turn = 0
    expansions = 0
    yielded: set[Term] = set()
    while expansions < 30_000 and (queues[0] or queues[1]):
        side = turn % 2
        if not queues[side]:
            side = 1 - side
        turn += 1
        term, depth = queues[side].popleft()
        expansions += 1
        if depth >= 5:
            yield None
            continue
        for changed, edge in _rewrite_edges(problem, term, pool):
            if term_size(changed) > 21 or changed in stores[side]:
                continue
            path_proof = transitivity(stores[side][term], edge)
            stores[side][changed] = path_proof
            queues[side].append((changed, depth + 1))
            if changed in stores[1 - side] and changed not in yielded:
                yielded.add(changed)
                if side == 0:
                    proof = transitivity(path_proof, symmetry(backward[changed]))
                else:
                    proof = transitivity(forward[changed], symmetry(path_proof))
                yield Candidate("derivation", proof)
        yield None


def _exhaustive_tables(order: int) -> Iterator[tuple[int, ...]]:
    yield from itertools.product(range(order), repeat=order * order)


def _rectangular_bands(order: int) -> Iterator[tuple[int, ...]]:
    for left_order in range(2, order):
        if order % left_order:
            continue
        right_order = order // left_order
        yield tuple(
            (left // right_order) * right_order + right % right_order
            for left in range(order)
            for right in range(order)
        )
        yield tuple(
            (right // right_order) * right_order + left % right_order
            for left in range(order)
            for right in range(order)
        )


def _product_affine_tables(order: int) -> Iterator[tuple[int, ...]]:
    for left_order in range(2, order):
        if order % left_order:
            continue
        right_order = order // left_order
        ranges = (
            range(left_order),
            range(left_order),
            range(left_order),
            range(right_order),
            range(right_order),
            range(right_order),
        )
        for coefficients in itertools.product(*ranges):
            if not any(coefficients):
                continue
            a1, b1, c1, a2, b2, c2 = coefficients
            cells = []
            for left in range(order):
                for right in range(order):
                    lx, ly = divmod(left, right_order)
                    rx, ry = divmod(right, right_order)
                    x = (a1 * lx + b1 * rx + c1) % left_order
                    y = (a2 * ly + b2 * ry + c2) % right_order
                    cells.append(x * right_order + y)
            yield tuple(cells)


def _projection_exceptions(order: int) -> Iterator[tuple[int, ...]]:
    bases = (
        tuple(left for left in range(order) for _ in range(order)),
        tuple(right for _ in range(order) for right in range(order)),
    )
    for base in bases:
        for cell, old_value in enumerate(base):
            for value in range(order):
                if value == old_value:
                    continue
                changed = list(base)
                changed[cell] = value
                yield tuple(changed)
        for row in range(order):
            for value in range(order):
                changed = list(base)
                changed[row * order : (row + 1) * order] = [value] * order
                yield tuple(changed)
        for column in range(order):
            for value in range(order):
                changed = list(base)
                for row in range(order):
                    changed[row * order + column] = value
                yield tuple(changed)


def _structured_tables(order: int) -> Iterator[tuple[int, ...]]:
    for constant in range(order):
        yield (constant,) * (order * order)
    yield tuple(left for left in range(order) for _ in range(order))
    yield tuple(right for _ in range(order) for right in range(order))
    yield tuple(min(left, right) for left in range(order) for right in range(order))
    yield tuple(max(left, right) for left in range(order) for right in range(order))
    yield tuple((left + right) % order for left in range(order) for right in range(order))
    yield tuple((left - right) % order for left in range(order) for right in range(order))
    for a, b, constant in itertools.product(range(order), repeat=3):
        yield tuple(
            (a * left + b * right + constant) % order
            for left in range(order)
            for right in range(order)
        )
    for constant in range(order):
        yield tuple(
            left if left == right else constant
            for left in range(order)
            for right in range(order)
        )
        yield tuple(
            left if left == right else left
            for left in range(order)
            for right in range(order)
        )
        yield tuple(
            left if left == right else right
            for left in range(order)
            for right in range(order)
        )
        yield tuple(
            left if left == right else (left + right + constant) % order
            for left in range(order)
            for right in range(order)
        )
    yield from _rectangular_bands(order)
    yield from _product_affine_tables(order)
    yield from _projection_exceptions(order)


def _evaluate_partial(
    term: Term, assignment: Sequence[int], order: int, cells: Sequence[int]
) -> int | None:
    if isinstance(term, Var):
        return assignment[term.slot]
    left = _evaluate_partial(term.left, assignment, order, cells)
    right = _evaluate_partial(term.right, assignment, order, cells)
    if left is None or right is None:
        return None
    value = cells[left * order + right]
    return None if value < 0 else value


def _premise_consistent(problem: Problem, order: int, cells: Sequence[int]) -> bool:
    for assignment in itertools.product(
        range(order), repeat=len(problem.premise.variables)
    ):
        left = _evaluate_partial(problem.premise.lhs, assignment, order, cells)
        right = _evaluate_partial(problem.premise.rhs, assignment, order, cells)
        if left is not None and right is not None and left != right:
            return False
    return True


def _countermodel_events(problem: Problem) -> Iterator[Candidate | None]:
    seen: set[tuple[int, tuple[int, ...]]] = set()
    retained: dict[int, list[tuple[int, ...]]] = {order: [] for order in range(4, 8)}

    def consider(
        order: int, cells: tuple[int, ...], retain: bool
    ) -> Candidate | None:
        key = (order, cells)
        if key in seen:
            return None
        seen.add(key)
        magma = FiniteMagma(order, cells)
        if not equation_holds(problem.premise, magma):
            return None
        if retain and len(retained[order]) < 4:
            retained[order].append(cells)
        if equation_holds(problem.goal, magma):
            return None
        return Candidate("countermodel", magma)

    for order in (2, 3):
        for cells in _exhaustive_tables(order):
            yield consider(order, tuple(cells), False)
    for order in range(4, 8):
        for cells in _structured_tables(order):
            yield consider(order, cells, True)

    order = 4
    cells = [-1] * (order * order)
    seeds = retained[order]

    def value_order(cell: int) -> tuple[int, ...]:
        return tuple(dict.fromkeys([seed[cell] for seed in seeds] + list(range(order))))

    def visit(cell: int) -> Iterator[Candidate | None]:
        for value in value_order(cell):
            cells[cell] = value
            consistent = _premise_consistent(problem, order, cells)
            yield None
            if not consistent:
                continue
            if cell + 1 == len(cells):
                candidate = consider(order, tuple(cells), False)
                if candidate is not None:
                    yield candidate
            else:
                yield from visit(cell + 1)
        cells[cell] = -1

    yield from visit(0)


def registered_strategies() -> tuple[Strategy, ...]:
    return (
        Strategy(
            "countermodel.portfolio",
            "1",
            LANE_COUNTERMODEL,
            lambda problem: _GeneratorSession(_countermodel_events(problem), 64),
        ),
        Strategy(
            "proof.closed_form",
            "1",
            LANE_PROOF,
            lambda problem: _GeneratorSession(_closed_form_events(problem), 8),
        ),
        Strategy(
            "proof.short_chain",
            "1",
            LANE_PROOF,
            lambda problem: _GeneratorSession(_short_chain_events(problem), 8),
        ),
        Strategy(
            "proof.specialized",
            "1",
            LANE_PROOF,
            lambda problem: _GeneratorSession(_specialized_events(problem), 8),
        ),
        Strategy(
            "proof.rewrite",
            "1",
            LANE_PROOF,
            lambda problem: _GeneratorSession(_rewrite_events(problem), 8),
        ),
    )


# ---------------------------------------------------------------------------
# Case engine


@dataclass(frozen=True, slots=True)
class BudgetProfile:
    version: str
    timeout_seconds: float
    minimum_judge_window_seconds: float
    shutdown_margin_seconds: float
    credits_per_turn: int = 1

    @property
    def work_seconds(self) -> float:
        return max(
            0.0,
            self.timeout_seconds
            - self.minimum_judge_window_seconds
            - self.shutdown_margin_seconds,
        )

    @classmethod
    def from_timeout(cls, timeout_seconds: float) -> "BudgetProfile":
        if timeout_seconds >= 300:
            return cls("solo-v1", timeout_seconds, 30.0, 2.0)
        judge_window = min(5.0, max(0.05, timeout_seconds * 0.1))
        margin = min(0.5, max(0.01, timeout_seconds * 0.02))
        return cls("solo-short-v1", timeout_seconds, judge_window, margin)


@dataclass(slots=True)
class _SessionRecord:
    strategy: Strategy
    session: StrategySession
    registry_index: int
    status: str = "active"
    credits_granted: int = 0
    credits_used: int = 0
    candidates_yielded: int = 0


@dataclass(frozen=True, slots=True)
class CaseOutcome:
    status: str
    verdict: str | None = None
    source: str | None = None
    reason: str | None = None


JudgeExchange = Callable[[str, str], Mapping[str, object]]
TraceRecorder = Callable[[Mapping[str, object]], None]


def _choose_lane(
    records: Sequence[_SessionRecord],
    first_turn: bool,
    preferred_lane: str | None,
    last_lane: str | None,
) -> str | None:
    active = {
        lane: [
            record
            for record in records
            if record.status == "active" and record.strategy.lane == lane
        ]
        for lane in (LANE_COUNTERMODEL, LANE_PROOF)
    }
    available = [lane for lane, lane_records in active.items() if lane_records]
    if not available:
        return None
    if len(available) == 1:
        return available[0]
    if first_turn:
        return preferred_lane or LANE_COUNTERMODEL
    credits = {
        lane: sum(
            record.credits_granted
            for record in records
            if record.strategy.lane == lane
        )
        for lane in available
    }
    if credits[LANE_COUNTERMODEL] < credits[LANE_PROOF]:
        return LANE_COUNTERMODEL
    if credits[LANE_PROOF] < credits[LANE_COUNTERMODEL]:
        return LANE_PROOF
    if last_lane == LANE_COUNTERMODEL:
        return LANE_PROOF
    if last_lane == LANE_PROOF:
        return LANE_COUNTERMODEL
    return LANE_COUNTERMODEL


def _choose_session(
    records: Sequence[_SessionRecord], lane: str
) -> _SessionRecord:
    return min(
        (
            record
            for record in records
            if record.status == "active" and record.strategy.lane == lane
        ),
        key=lambda record: (record.credits_granted, record.registry_index),
    )


def _safe_record(recorder: TraceRecorder, record: Mapping[str, object]) -> None:
    try:
        recorder(record)
    except Exception:
        pass


def run_case(
    start_message: Mapping[str, object],
    judge_exchange: JudgeExchange,
    trace_recorder: TraceRecorder,
) -> CaseOutcome:
    started = time.monotonic()
    try:
        public_problem = start_message["problem"]
        budget_data = start_message["budget"]
        if not isinstance(public_problem, Mapping) or not isinstance(budget_data, Mapping):
            raise ValueError("startup problem and budget must be objects")
        timeout_seconds = float(budget_data["timeout_seconds"])
        if timeout_seconds <= 0:
            raise ValueError("timeout must be positive")
        limits = Limits(
            int(budget_data["max_code_length"]),
            int(budget_data["max_false_cert_bytes"]),
        )
        if limits.max_code_length <= 0 or limits.max_false_cert_bytes <= 0:
            raise ValueError("certificate limits must be positive")
        problem = parse_problem(public_problem)
    except (KeyError, TypeError, ValueError) as error:
        _safe_record(trace_recorder, {"event": "startup_rejected", "reason": str(error)})
        return CaseOutcome("error", reason=str(error))

    profile = BudgetProfile.from_timeout(timeout_seconds)
    hard_deadline = started + profile.timeout_seconds
    work_cutoff = started + profile.work_seconds
    strategies = registered_strategies()
    run_id = _digest(
        (
            problem.fingerprint,
            profile.version,
            tuple((strategy.id, strategy.version) for strategy in strategies),
        )
    )
    _safe_record(
        trace_recorder,
        {
            "event": "case_start",
            "schema": 1,
            "case_run_id": run_id,
            "problem_fingerprint": problem.fingerprint,
            "budget_profile": profile.version,
            "oracle_mode": ORACLE_MODE,
            "strategies": [
                {"id": strategy.id, "version": strategy.version, "lane": strategy.lane}
                for strategy in strategies
            ],
        },
    )

    oracle = OracleSubsystem(ORACLE_MODE, ORACLE_ARTIFACT)
    oracle_result = oracle.consult(
        problem, public_problem.get("eq1_id"), public_problem.get("eq2_id")
    )
    _safe_record(
        trace_recorder,
        {
            "event": "oracle_consulted",
            "mode": ORACLE_MODE,
            "disposition": oracle_result.disposition,
            "preferred_lane": oracle_result.preferred_lane,
        },
    )
    seen = SeenCandidates()

    if oracle_result.cached_candidate is not None and time.monotonic() < work_cutoff:
        admission = admit(problem, oracle_result.cached_candidate, limits, seen)
        _safe_record(
            trace_recorder,
            {
                "event": "oracle_candidate",
                "admission": admission.status,
                "reason": admission.reason,
                "evidence_fingerprint": admission.evidence_fingerprint,
            },
        )
        if admission.status == "judge_request" and time.monotonic() < work_cutoff:
            assert admission.verdict is not None and admission.source is not None
            response = judge_exchange(admission.verdict, admission.source)
            status = str(response.get("status", "error"))
            if status == "accepted":
                return CaseOutcome("accepted", admission.verdict, admission.source)
            if status not in (
                "incorrect",
                "incomplete_proof",
                "malformed",
                "unparsed",
            ):
                return CaseOutcome("error", reason="judge infrastructure error")
        oracle_result = replace(oracle_result, preferred_lane=None, disposition="invalid")

    records = [
        _SessionRecord(strategy, strategy.open(problem), index)
        for index, strategy in enumerate(strategies)
    ]
    first_turn = True
    last_lane: str | None = None

    while time.monotonic() < work_cutoff:
        lane = _choose_lane(
            records,
            first_turn,
            oracle_result.preferred_lane,
            last_lane,
        )
        if lane is None:
            _safe_record(trace_recorder, {"event": "case_stop", "reason": "search_exhausted"})
            return CaseOutcome("unsolved", reason="search_exhausted")
        record = _choose_session(records, lane)
        first_turn = False
        last_lane = lane
        record.credits_granted += profile.credits_per_turn
        _safe_record(
            trace_recorder,
            {
                "event": "strategy_grant",
                "strategy_id": record.strategy.id,
                "lane": lane,
                "credits_granted": record.credits_granted,
            },
        )
        result = record.session.advance(
            EffortBudget(profile.credits_per_turn, work_cutoff)
        )
        record.credits_used += result.credits_used
        if result.status in ("exhausted", "fault"):
            record.status = result.status
        _safe_record(
            trace_recorder,
            {
                "event": "strategy_advance",
                "strategy_id": record.strategy.id,
                "status": result.status,
                "credits_used": record.credits_used,
                "fault": result.fault,
            },
        )
        if result.status != "yielded" or result.candidate is None:
            continue
        if time.monotonic() >= work_cutoff:
            break

        record.candidates_yielded += 1
        candidate = replace(
            result.candidate,
            provenance=Provenance(
                record.strategy.id,
                record.strategy.version,
                record.candidates_yielded,
                record.credits_used,
            ),
        )
        admission = admit(problem, candidate, limits, seen)
        if candidate.provenance is not None:
            candidate = replace(
                candidate,
                provenance=replace(
                    candidate.provenance,
                    evidence_fingerprint=admission.evidence_fingerprint,
                ),
            )
        _safe_record(
            trace_recorder,
            {
                "event": "candidate_admission",
                "strategy_id": record.strategy.id,
                "candidate_index": record.candidates_yielded,
                "kind": candidate.kind,
                "status": admission.status,
                "reason": admission.reason,
                "evidence_fingerprint": admission.evidence_fingerprint,
                "request_fingerprint": admission.request_fingerprint,
                "rendered_bytes": len(admission.source.encode("utf-8")) if admission.source else 0,
            },
        )
        if admission.status != "judge_request":
            continue
        if time.monotonic() >= work_cutoff:
            break
        assert admission.verdict is not None and admission.source is not None
        judge_started = time.monotonic()
        try:
            response = judge_exchange(admission.verdict, admission.source)
        except Exception as error:
            _safe_record(
                trace_recorder,
                {"event": "judge_error", "reason": f"{type(error).__name__}: {error}"},
            )
            return CaseOutcome("error", reason="judge exchange failed")
        status = str(response.get("status", "error"))
        _safe_record(
            trace_recorder,
            {
                "event": "judge_result",
                "strategy_id": record.strategy.id,
                "candidate_index": record.candidates_yielded,
                "status": status,
                "elapsed_seconds": round(time.monotonic() - judge_started, 6),
                "request_fingerprint": admission.request_fingerprint,
            },
        )
        if status == "accepted":
            return CaseOutcome("accepted", admission.verdict, admission.source)
        if status not in (
            "incorrect",
            "incomplete_proof",
            "malformed",
            "unparsed",
        ):
            return CaseOutcome("error", reason="judge infrastructure error")

    reason = "hard_deadline" if time.monotonic() >= hard_deadline else "work_cutoff"
    _safe_record(trace_recorder, {"event": "case_stop", "reason": reason})
    return CaseOutcome("unsolved", reason=reason)


# ---------------------------------------------------------------------------
# stdin/stdout adapter and main


def _read_message() -> Mapping[str, object]:
    line = sys.stdin.readline()
    if not line:
        raise EOFError("startup message missing")
    message = json.loads(line)
    if not isinstance(message, Mapping):
        raise ValueError("startup message must be an object")
    return message


def _judge_exchange(verdict: str, source: str) -> Mapping[str, object]:
    print(
        json.dumps({"call": "judge", "verdict": verdict, "code": source}),
        flush=True,
    )
    line = sys.stdin.readline()
    if not line:
        raise EOFError("judge response missing")
    response = json.loads(line)
    if not isinstance(response, Mapping):
        raise ValueError("judge response must be an object")
    return response


def _trace_recorder(record: Mapping[str, object]) -> None:
    print(
        TRACE_PREFIX
        + json.dumps(record, ensure_ascii=False, separators=(",", ":"), sort_keys=True),
        file=sys.stderr,
        flush=True,
    )


def main() -> None:
    try:
        startup = _read_message()
        run_case(startup, _judge_exchange, _trace_recorder)
    except Exception as error:
        _trace_recorder(
            {"event": "solver_error", "reason": f"{type(error).__name__}: {error}"}
        )


if __name__ == "__main__":
    main()
