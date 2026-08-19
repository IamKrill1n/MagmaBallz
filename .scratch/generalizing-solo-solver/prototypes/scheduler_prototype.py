#!/usr/bin/env python3
"""PROTOTYPE — drive a deterministic Solo scheduler state model.

Question: does a one-credit, lane-fair scheduler preserve deterministic work
order while giving proof and countermodel search bounded access, limiting an
optional direction hint to the first slice, and guarding local certificate work
and synchronous judge calls under the versioned 300-second budget profile?

This is throwaway instrumentation for the Wayfinder ticket "Define
deterministic scheduler and budget accounting". It does not implement a solver.
Run it from the repository root with:

    python3 .scratch/generalizing-solo-solver/prototypes/scheduler_prototype.py

For a non-interactive tour of the proposed invariants:

    python3 .scratch/generalizing-solo-solver/prototypes/scheduler_prototype.py --batch
"""

from __future__ import annotations

import argparse

from scheduler_model import (
    LANE_COUNTERMODEL,
    LANE_PROOF,
    SchedulerState,
    begin_slice,
    complete_admission,
    complete_advance,
    complete_judge,
    elapse,
    new_state,
)


BOLD = "\x1b[1m"
DIM = "\x1b[2m"
RESET = "\x1b[0m"
CLEAR = "\x1b[2J\x1b[H"


def lane_totals(state: SchedulerState, lane: str) -> tuple[int, int]:
    sessions = tuple(item for item in state.sessions if item.lane == lane)
    return (
        sum(item.credits_granted for item in sessions),
        sum(item.credits_used for item in sessions),
    )


def render(state: SchedulerState, *, clear: bool = True) -> None:
    if clear:
        print(CLEAR, end="")
    profile = state.profile
    print(f"{BOLD}Deterministic scheduler prototype{RESET}")
    print(f"{DIM}PROTOTYPE — no production solver code{RESET}\n")
    print(f"{BOLD}phase{RESET}: {state.phase}")
    print(f"{BOLD}hint{RESET}: {state.preferred_lane or 'none'}")
    print(f"{BOLD}elapsed{RESET}: {state.elapsed_seconds:.1f}s / {profile.timeout_seconds:.1f}s")
    print(f"{BOLD}work cutoff{RESET}: {profile.work_cutoff_seconds:.1f}s")
    print(f"{BOLD}advancing{RESET}: {state.advancing_strategy or '-'}")
    candidate = state.pending_candidate
    print(
        f"{BOLD}candidate{RESET}: "
        f"{candidate.strategy_id + ' / ' + candidate.kind if candidate else '-'}"
    )
    print(f"{BOLD}stop reason{RESET}: {state.stop_reason or '-'}\n")

    countermodel = lane_totals(state, LANE_COUNTERMODEL)
    proof = lane_totals(state, LANE_PROOF)
    print(f"{BOLD}lane credits (granted / used){RESET}")
    print(f"  countermodel: {countermodel[0]} / {countermodel[1]}")
    print(f"  proof:        {proof[0]} / {proof[1]}\n")

    print(f"{BOLD}strategy sessions{RESET}")
    for session in state.sessions:
        print(
            f"  {session.strategy_id:25} {session.status:9} "
            f"grant={session.credits_granted:<3} used={session.credits_used:<3} "
            f"advance={session.advances:<3} candidates={session.candidates_yielded}"
        )

    ledger = state.ledger
    print(f"\n{BOLD}non-fungible work ledger{RESET}")
    print(f"  kernel work units:  {ledger.kernel_work_units}")
    print(f"  rendered bytes:     {ledger.rendered_bytes}")
    print(f"  local admissible:   {ledger.locally_admissible}")
    print(f"  local rejected:     {ledger.locally_rejected}")
    print(f"  judge calls/seconds:{ledger.judge_calls} / {ledger.judge_seconds:.1f}")

    print(f"\n{BOLD}recent trace{RESET}")
    for item in state.trace[-8:]:
        print(f"  {DIM}{item}{RESET}")

    if state.phase == "ready":
        shortcuts = "[g] grant next slice  [t] +30s  [1/2/3] reset hint  [q] quit"
    elif state.phase == "advancing":
        shortcuts = "[p] paused  [y] yielded  [x] exhausted  [f] fault  [t] +30s"
    elif state.phase == "candidate_admission":
        shortcuts = "[v] locally admissible  [l] local reject  [t] +30s"
    elif state.phase == "awaiting_judge":
        shortcuts = "[a] accepted  [r] reject (3s)  [s] slow reject (35s)  [t] +30s"
    else:
        shortcuts = "[1/2/3] reset hint  [q] quit"
    print(f"\n{BOLD}{shortcuts}{RESET}")


def reset_for_key(key: str) -> SchedulerState:
    hints = {"1": None, "2": LANE_COUNTERMODEL, "3": LANE_PROOF}
    return new_state(hints[key])


def interactive(initial_hint: str | None) -> None:
    state = new_state(initial_hint)
    while True:
        render(state)
        key = input("\n> ").strip().lower()[:1]
        try:
            if key == "q":
                return
            if key in ("1", "2", "3"):
                state = reset_for_key(key)
            elif key == "t":
                state = elapse(state, 30.0)
            elif state.phase == "ready" and key == "g":
                state = begin_slice(state)
            elif state.phase == "advancing" and key in ("p", "y", "x", "f"):
                statuses = {
                    "p": "paused",
                    "y": "yielded",
                    "x": "exhausted",
                    "f": "fault",
                }
                state = complete_advance(state, statuses[key])
            elif state.phase == "candidate_admission" and key in ("v", "l"):
                state = complete_admission(
                    state,
                    admissible=key == "v",
                    kernel_work_units=5,
                    rendered_bytes=1200 if key == "v" else 0,
                )
            elif state.phase == "awaiting_judge" and key in ("a", "r", "s"):
                state = complete_judge(
                    state,
                    "accepted" if key == "a" else "incorrect",
                    elapsed_seconds=35.0 if key == "s" else 3.0,
                )
        except ValueError as error:
            state = SchedulerState(
                **{**state.__dict__, "trace": state.trace + (f"invalid action: {error}",)}
            )


def run_paused_turn(state: SchedulerState, elapsed_seconds: float = 1.0) -> SchedulerState:
    return complete_advance(
        begin_slice(state),
        "paused",
        elapsed_seconds=elapsed_seconds,
    )


def print_scenario(name: str, state: SchedulerState) -> None:
    print(f"\n=== {name} ===")
    render(state, clear=False)


def batch() -> None:
    no_hint = new_state()
    for _ in range(8):
        no_hint = run_paused_turn(no_hint)
    print_scenario("No hint: equal lane entitlement, proof priority", no_hint)

    proof_hint = new_state(LANE_PROOF)
    for _ in range(8):
        proof_hint = run_paused_turn(proof_hint)
    print_scenario("Proof hint: first slice changes, entitlement does not", proof_hint)

    rejected = new_state()
    rejected = begin_slice(rejected)
    rejected = complete_advance(rejected, "yielded")
    rejected = complete_admission(
        rejected,
        admissible=True,
        kernel_work_units=5,
        rendered_bytes=1200,
    )
    rejected = complete_judge(rejected, "incorrect", elapsed_seconds=8.0)
    rejected = run_paused_turn(rejected)
    print_scenario("Rejected candidate: synchronous judge then fair rotation", rejected)

    cutoff = new_state(elapsed_seconds=267.0)
    cutoff = begin_slice(cutoff)
    cutoff = complete_advance(cutoff, "yielded", elapsed_seconds=0.2)
    cutoff = complete_admission(
        cutoff,
        admissible=True,
        kernel_work_units=5,
        rendered_bytes=1200,
        elapsed_seconds=0.2,
    )
    cutoff = complete_judge(cutoff, "incorrect", elapsed_seconds=35.0)
    print_scenario("Slow judge: empirical 30s window can still overrun", cutoff)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batch", action="store_true")
    parser.add_argument(
        "--hint",
        choices=("none", LANE_COUNTERMODEL, LANE_PROOF),
        default="none",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.batch:
        batch()
        return
    hint = None if args.hint == "none" else args.hint
    interactive(hint)


if __name__ == "__main__":
    main()
