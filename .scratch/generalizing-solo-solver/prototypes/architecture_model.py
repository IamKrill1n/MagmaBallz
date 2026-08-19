"""Pure state model for the throwaway Solo architecture prototype."""

from __future__ import annotations

from dataclasses import dataclass, replace


@dataclass(frozen=True)
class ModuleSpec:
    name: str
    depends_on: tuple[str, ...]
    interface: str


MODULES = (
    ModuleSpec("solver kernel", (), "parse_problem; admit; immutable values"),
    ModuleSpec("oracle subsystem", ("solver kernel",), "consult"),
    ModuleSpec("strategy registry", ("solver kernel",), "registered_strategies"),
    ModuleSpec(
        "case engine",
        ("solver kernel", "oracle subsystem", "strategy registry"),
        "run_case",
    ),
    ModuleSpec("stdio adapter", ("case engine",), "main"),
)


@dataclass(frozen=True)
class BuildStage:
    name: str
    blocked_by: tuple[str, ...]


BUILD_STAGES = (
    BuildStage("submission spine", ()),
    BuildStage("kernel vertical slice", ("submission spine",)),
    BuildStage("case engine", ("kernel vertical slice",)),
    BuildStage("countermodel portfolio", ("case engine",)),
    BuildStage("proof strategies", ("case engine",)),
    BuildStage(
        "composition benchmark",
        ("countermodel portfolio", "proof strategies"),
    ),
    BuildStage("oracle contracts", ("composition benchmark",)),
    BuildStage("artifact and hardening", ("oracle contracts",)),
)


SCENARIOS = ("disabled", "cache_hit", "direction_hint", "invalid_oracle")


@dataclass(frozen=True)
class ArchitectureState:
    scenario: str
    phase: str = "startup"
    owner: str = "stdio adapter"
    oracle_mode: str = "disabled"
    oracle_disposition: str = "not_consulted"
    artifact_touched: bool = False
    preferred_lane: str | None = None
    first_lane: str | None = None
    reasoning_opened: bool = False
    candidate_source: str | None = None
    candidates_admitted: int = 0
    judge_calls: int = 0
    outcome: str | None = None
    trace: tuple[str, ...] = ("startup received",)


def new_state(scenario: str = "disabled") -> ArchitectureState:
    if scenario not in SCENARIOS:
        raise ValueError(f"unknown scenario: {scenario}")
    mode = "disabled" if scenario == "disabled" else "enabled"
    return ArchitectureState(scenario=scenario, oracle_mode=mode)


def _append(state: ArchitectureState, message: str) -> ArchitectureState:
    return replace(state, trace=state.trace + (message,))


def consult_oracle(state: ArchitectureState) -> ArchitectureState:
    if state.phase != "startup":
        raise ValueError("the oracle is consulted exactly once after startup")

    if state.scenario == "disabled":
        return _append(
            replace(
                state,
                phase="search_unopened",
                owner="case engine",
                oracle_disposition="disabled",
                artifact_touched=False,
            ),
            "oracle disabled: artifact and pair IDs bypassed",
        )

    if state.scenario == "cache_hit":
        return _append(
            replace(
                state,
                phase="candidate_admission",
                owner="solver kernel",
                oracle_disposition="hit",
                artifact_touched=True,
                preferred_lane="proof",
                candidate_source="oracle.cache",
            ),
            "oracle hit: cached candidate sent to ordinary admission",
        )

    if state.scenario == "direction_hint":
        return _append(
            replace(
                state,
                phase="search_unopened",
                owner="case engine",
                oracle_disposition="miss",
                artifact_touched=True,
                preferred_lane="proof",
            ),
            "oracle miss: proof preference retained for first turn only",
        )

    return _append(
        replace(
            state,
            phase="search_unopened",
            owner="case engine",
            oracle_disposition="invalid",
            artifact_touched=True,
            preferred_lane=None,
        ),
        "oracle invalid: preference cleared and reasoning remains neutral",
    )


def open_reasoning(state: ArchitectureState) -> ArchitectureState:
    if state.phase != "search_unopened":
        raise ValueError("reasoning opens only after the oracle path completes")
    first_lane = state.preferred_lane or "countermodel"
    return _append(
        replace(
            state,
            phase="searching",
            owner="case engine",
            first_lane=first_lane,
            preferred_lane=None,
            reasoning_opened=True,
        ),
        f"sessions opened; first turn={first_lane}; hint consumed",
    )


def advance_search(state: ArchitectureState, result: str) -> ArchitectureState:
    if state.phase != "searching":
        raise ValueError("a strategy advances only while searching")
    if result == "paused":
        return _append(state, "strategy paused; case engine selects next turn")
    if result == "candidate":
        return _append(
            replace(
                state,
                phase="candidate_admission",
                owner="solver kernel",
                candidate_source="strategy",
            ),
            "strategy yielded candidate to ordinary admission",
        )
    if result == "exhausted":
        return _append(
            replace(
                state,
                phase="stopped",
                owner="case engine",
                outcome="search_exhausted",
            ),
            "all sessions terminal; exit unsolved",
        )
    raise ValueError(f"unsupported search result: {result}")


def admit_candidate(
    state: ArchitectureState, *, admissible: bool
) -> ArchitectureState:
    if state.phase != "candidate_admission" or state.candidate_source is None:
        raise ValueError("there is no candidate awaiting admission")
    source = state.candidate_source
    if admissible:
        return _append(
            replace(
                state,
                phase="awaiting_judge",
                owner="stdio adapter",
                candidates_admitted=state.candidates_admitted + 1,
            ),
            f"{source} candidate locally admissible; exact source rendered",
        )

    if source == "oracle.cache":
        return _append(
            replace(
                state,
                phase="search_unopened",
                owner="case engine",
                oracle_disposition="invalid",
                preferred_lane=None,
                candidate_source=None,
            ),
            "cached candidate rejected locally; oracle hint cleared",
        )
    return _append(
        replace(
            state,
            phase="searching",
            owner="case engine",
            candidate_source=None,
        ),
        "strategy candidate rejected locally; session receives no feedback",
    )


def complete_judge(state: ArchitectureState, status: str) -> ArchitectureState:
    if state.phase != "awaiting_judge" or state.candidate_source is None:
        raise ValueError("there is no candidate awaiting the judge")
    if status not in ("accepted", "incorrect", "error"):
        raise ValueError(f"unsupported judge status: {status}")

    state = replace(state, judge_calls=state.judge_calls + 1)
    if status == "accepted":
        return _append(
            replace(
                state,
                phase="stopped",
                owner="case engine",
                outcome="accepted",
            ),
            "judge accepted; proxy records result and case terminates",
        )
    if status == "error":
        return _append(
            replace(
                state,
                phase="stopped",
                owner="case engine",
                outcome="judge_infrastructure_error",
            ),
            "judge infrastructure error; case terminates without fallback",
        )

    if state.candidate_source == "oracle.cache":
        return _append(
            replace(
                state,
                phase="search_unopened",
                owner="case engine",
                oracle_disposition="invalid",
                preferred_lane=None,
                candidate_source=None,
            ),
            "cached candidate rejected by judge; oracle hint cleared",
        )
    return _append(
        replace(
            state,
            phase="searching",
            owner="case engine",
            candidate_source=None,
        ),
        "strategy candidate rejected by judge; fair search resumes",
    )


def reach_cutoff(state: ArchitectureState) -> ArchitectureState:
    if state.phase not in ("search_unopened", "searching"):
        raise ValueError("cutoff is checked before new search/admission/judge work")
    return _append(
        replace(
            state,
            phase="stopped",
            owner="case engine",
            outcome="work_cutoff",
        ),
        "work cutoff reached; exit without unverified fallback",
    )


def validate_static_design() -> tuple[str, ...]:
    module_names: set[str] = set()
    for module in MODULES:
        missing = tuple(dep for dep in module.depends_on if dep not in module_names)
        if missing:
            raise ValueError(f"module {module.name} precedes dependencies {missing}")
        module_names.add(module.name)

    stage_names: set[str] = set()
    for stage in BUILD_STAGES:
        missing = tuple(dep for dep in stage.blocked_by if dep not in stage_names)
        if missing:
            raise ValueError(f"stage {stage.name} precedes blockers {missing}")
        stage_names.add(stage.name)

    return (
        "module dependency order is acyclic",
        "build stages follow their declared blockers",
        "stdio is the only module above the case-engine interface",
    )
