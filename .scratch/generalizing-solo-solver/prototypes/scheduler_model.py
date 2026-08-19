"""Pure state model for the throwaway deterministic-scheduler prototype."""

from __future__ import annotations

from dataclasses import dataclass, replace


LANE_COUNTERMODEL = "countermodel"
LANE_PROOF = "proof"
ACTIVE = "active"


@dataclass(frozen=True)
class BudgetProfile:
    timeout_seconds: float = 300.0
    minimum_judge_window_seconds: float = 30.0
    shutdown_margin_seconds: float = 2.0
    credits_per_turn: int = 1

    @property
    def work_cutoff_seconds(self) -> float:
        return max(
            0.0,
            self.timeout_seconds
            - self.minimum_judge_window_seconds
            - self.shutdown_margin_seconds,
        )


@dataclass(frozen=True)
class SessionState:
    strategy_id: str
    lane: str
    registry_index: int
    status: str = ACTIVE
    credits_granted: int = 0
    credits_used: int = 0
    advances: int = 0
    candidates_yielded: int = 0


@dataclass(frozen=True)
class CandidateState:
    strategy_id: str
    lane: str
    kind: str


@dataclass(frozen=True)
class WorkLedger:
    kernel_work_units: int = 0
    rendered_bytes: int = 0
    locally_rejected: int = 0
    locally_admissible: int = 0
    judge_calls: int = 0
    judge_seconds: float = 0.0


@dataclass(frozen=True)
class SchedulerState:
    profile: BudgetProfile
    preferred_lane: str | None
    elapsed_seconds: float
    phase: str
    sessions: tuple[SessionState, ...]
    ledger: WorkLedger = WorkLedger()
    first_search_grant: bool = True
    last_lane: str | None = None
    advancing_strategy: str | None = None
    pending_candidate: CandidateState | None = None
    stop_reason: str | None = None
    trace: tuple[str, ...] = ()


def new_state(
    preferred_lane: str | None = None,
    *,
    profile: BudgetProfile | None = None,
    elapsed_seconds: float = 0.0,
) -> SchedulerState:
    if preferred_lane not in (None, LANE_COUNTERMODEL, LANE_PROOF):
        raise ValueError("preferred_lane must be proof, countermodel, or None")
    sessions = (
        SessionState("countermodel.portfolio", LANE_COUNTERMODEL, 0),
        SessionState("proof.closed_form", LANE_PROOF, 1),
        SessionState("proof.short_chain", LANE_PROOF, 2),
        SessionState("proof.specialized", LANE_PROOF, 3),
        SessionState("proof.rewrite", LANE_PROOF, 4),
    )
    return SchedulerState(
        profile=profile or BudgetProfile(),
        preferred_lane=preferred_lane,
        elapsed_seconds=elapsed_seconds,
        phase="ready",
        sessions=sessions,
        trace=(f"start hint={preferred_lane or 'none'}",),
    )


def _append(state: SchedulerState, message: str) -> SchedulerState:
    return replace(state, trace=state.trace + (message,))


def _replace_session(
    state: SchedulerState, changed: SessionState
) -> SchedulerState:
    sessions = tuple(
        changed if item.strategy_id == changed.strategy_id else item
        for item in state.sessions
    )
    return replace(state, sessions=sessions)


def _active_by_lane(state: SchedulerState) -> dict[str, tuple[SessionState, ...]]:
    return {
        lane: tuple(
            item
            for item in state.sessions
            if item.lane == lane and item.status == ACTIVE
        )
        for lane in (LANE_COUNTERMODEL, LANE_PROOF)
    }


def _lane_credits(state: SchedulerState, lane: str) -> int:
    return sum(item.credits_granted for item in state.sessions if item.lane == lane)


def _choose_lane(state: SchedulerState) -> str | None:
    active = _active_by_lane(state)
    available = tuple(lane for lane, sessions in active.items() if sessions)
    if not available:
        return None
    if len(available) == 1:
        return available[0]

    if state.first_search_grant:
        return state.preferred_lane or LANE_COUNTERMODEL

    countermodel_credits = _lane_credits(state, LANE_COUNTERMODEL)
    proof_credits = _lane_credits(state, LANE_PROOF)
    if countermodel_credits < proof_credits:
        return LANE_COUNTERMODEL
    if proof_credits < countermodel_credits:
        return LANE_PROOF

    if state.last_lane == LANE_COUNTERMODEL:
        return LANE_PROOF
    if state.last_lane == LANE_PROOF:
        return LANE_COUNTERMODEL
    return LANE_COUNTERMODEL


def _choose_session(state: SchedulerState, lane: str) -> SessionState:
    return min(
        (
            item
            for item in state.sessions
            if item.lane == lane and item.status == ACTIVE
        ),
        key=lambda item: (item.credits_granted, item.registry_index),
    )


def begin_slice(state: SchedulerState) -> SchedulerState:
    if state.phase != "ready":
        raise ValueError("a slice can begin only while the scheduler is ready")
    if state.elapsed_seconds >= state.profile.work_cutoff_seconds:
        return _append(
            replace(state, phase="stopped", stop_reason="work_cutoff_reached"),
            "stop: work cutoff reached",
        )

    lane = _choose_lane(state)
    if lane is None:
        return _append(
            replace(state, phase="stopped", stop_reason="search_exhausted"),
            "stop: every strategy is exhausted or faulted",
        )

    session = _choose_session(state, lane)
    session = replace(
        session,
        credits_granted=(
            session.credits_granted + state.profile.credits_per_turn
        ),
    )
    state = _replace_session(state, session)
    state = replace(
        state,
        phase="advancing",
        first_search_grant=False,
        last_lane=lane,
        advancing_strategy=session.strategy_id,
    )
    return _append(
        state,
        f"grant {state.profile.credits_per_turn} credit to {session.strategy_id}",
    )


def complete_advance(
    state: SchedulerState,
    status: str,
    *,
    credits_used: int = 1,
    elapsed_seconds: float = 1.0,
) -> SchedulerState:
    if state.phase != "advancing" or state.advancing_strategy is None:
        raise ValueError("there is no advancing strategy")
    if status not in ("paused", "yielded", "exhausted", "fault"):
        raise ValueError("unsupported advance status")
    if not 0 <= credits_used <= state.profile.credits_per_turn:
        raise ValueError("credits_used must fit within the granted turn")

    session = next(
        item
        for item in state.sessions
        if item.strategy_id == state.advancing_strategy
    )
    candidate = None
    next_status = session.status
    yielded = session.candidates_yielded
    if status == "yielded":
        kind = "countermodel" if session.lane == LANE_COUNTERMODEL else "derivation"
        candidate = CandidateState(session.strategy_id, session.lane, kind)
        yielded += 1
    elif status in ("exhausted", "fault"):
        next_status = status

    session = replace(
        session,
        status=next_status,
        credits_used=session.credits_used + credits_used,
        advances=session.advances + 1,
        candidates_yielded=yielded,
    )
    state = _replace_session(state, session)
    state = replace(
        state,
        elapsed_seconds=state.elapsed_seconds + elapsed_seconds,
        phase="candidate_admission" if candidate else "ready",
        advancing_strategy=None,
        pending_candidate=candidate,
    )
    state = _append(
        state,
        f"{session.strategy_id} -> {status}; used={credits_used}",
    )

    if state.elapsed_seconds > state.profile.timeout_seconds:
        return _append(
            replace(
                state,
                phase="stopped",
                pending_candidate=None,
                stop_reason="hard_deadline_overrun",
            ),
            "stop: hard deadline overrun",
        )
    if candidate and state.elapsed_seconds >= state.profile.work_cutoff_seconds:
        return _append(
            replace(
                state,
                phase="stopped",
                pending_candidate=None,
                stop_reason="candidate_deferred_at_cutoff",
            ),
            "stop: yielded candidate cannot enter admission before cutoff",
        )
    if not candidate and state.elapsed_seconds >= state.profile.work_cutoff_seconds:
        return _append(
            replace(state, phase="stopped", stop_reason="work_cutoff_reached"),
            "stop: work cutoff reached",
        )
    return state


def complete_admission(
    state: SchedulerState,
    *,
    admissible: bool,
    kernel_work_units: int = 1,
    rendered_bytes: int = 0,
    elapsed_seconds: float = 0.2,
) -> SchedulerState:
    if state.phase != "candidate_admission" or state.pending_candidate is None:
        raise ValueError("there is no candidate awaiting admission")

    ledger = replace(
        state.ledger,
        kernel_work_units=state.ledger.kernel_work_units + kernel_work_units,
        rendered_bytes=state.ledger.rendered_bytes + rendered_bytes,
        locally_admissible=(
            state.ledger.locally_admissible + (1 if admissible else 0)
        ),
        locally_rejected=(
            state.ledger.locally_rejected + (0 if admissible else 1)
        ),
    )
    state = replace(
        state,
        elapsed_seconds=state.elapsed_seconds + elapsed_seconds,
        ledger=ledger,
    )
    if state.elapsed_seconds > state.profile.timeout_seconds:
        return _append(
            replace(
                state,
                phase="stopped",
                pending_candidate=None,
                stop_reason="hard_deadline_overrun",
            ),
            "stop: hard deadline overrun during admission",
        )
    if not admissible:
        state = _append(
            replace(state, phase="ready", pending_candidate=None),
            "candidate rejected locally",
        )
        if state.elapsed_seconds >= state.profile.work_cutoff_seconds:
            return _append(
                replace(state, phase="stopped", stop_reason="work_cutoff_reached"),
                "stop: work cutoff reached",
            )
        return state

    if state.elapsed_seconds >= state.profile.work_cutoff_seconds:
        return _append(
            replace(
                state,
                phase="stopped",
                pending_candidate=None,
                stop_reason="judge_window_unavailable",
            ),
            "stop: locally admissible candidate lacks the minimum judge window",
        )
    return _append(
        replace(state, phase="awaiting_judge"),
        "candidate locally admissible; judge call starts synchronously",
    )


def complete_judge(
    state: SchedulerState,
    status: str,
    *,
    elapsed_seconds: float = 3.0,
) -> SchedulerState:
    if state.phase != "awaiting_judge" or state.pending_candidate is None:
        raise ValueError("there is no active judge call")
    if status not in (
        "accepted",
        "incorrect",
        "incomplete_proof",
        "malformed",
        "unparsed",
        "error",
    ):
        raise ValueError("unsupported judge status")

    ledger = replace(
        state.ledger,
        judge_calls=state.ledger.judge_calls + 1,
        judge_seconds=state.ledger.judge_seconds + elapsed_seconds,
    )
    state = replace(
        state,
        elapsed_seconds=state.elapsed_seconds + elapsed_seconds,
        ledger=ledger,
    )
    if state.elapsed_seconds > state.profile.timeout_seconds:
        return _append(
            replace(
                state,
                phase="stopped",
                pending_candidate=None,
                stop_reason="hard_deadline_overrun",
            ),
            f"judge {status} arrived after the hard deadline",
        )
    if status == "accepted":
        return _append(
            replace(state, phase="solved", stop_reason="judge_accepted"),
            "judge accepted candidate; stop immediately",
        )
    if status == "error":
        return _append(
            replace(
                state,
                phase="stopped",
                pending_candidate=None,
                stop_reason="judge_infrastructure_error",
            ),
            "stop: judge infrastructure error",
        )

    state = _append(
        replace(state, phase="ready", pending_candidate=None),
        f"judge rejected candidate with {status}",
    )
    if state.elapsed_seconds >= state.profile.work_cutoff_seconds:
        return _append(
            replace(state, phase="stopped", stop_reason="work_cutoff_reached"),
            "stop: work cutoff reached after judge response",
        )
    return state


def elapse(state: SchedulerState, seconds: float) -> SchedulerState:
    if seconds < 0:
        raise ValueError("elapsed seconds must be nonnegative")
    state = replace(state, elapsed_seconds=state.elapsed_seconds + seconds)
    state = _append(state, f"clock advanced by {seconds:g}s")
    if state.elapsed_seconds > state.profile.timeout_seconds:
        return _append(
            replace(
                state,
                phase="stopped",
                pending_candidate=None,
                advancing_strategy=None,
                stop_reason="hard_deadline_overrun",
            ),
            "stop: hard deadline overrun",
        )
    return state
