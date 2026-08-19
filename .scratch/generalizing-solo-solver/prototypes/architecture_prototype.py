#!/usr/bin/env python3
"""PROTOTYPE — drive the proposed generalized Solo case architecture.

Question: does the proposed case-engine state model keep oracle, search,
admission, judging, and termination ownership clear when pushed through cache,
hint, rejection, and cutoff scenarios?

This is throwaway planning instrumentation, not production solver code. Run:

    python3 .scratch/generalizing-solo-solver/prototypes/architecture_prototype.py
    python3 .scratch/generalizing-solo-solver/prototypes/architecture_prototype.py --batch
"""

from __future__ import annotations

import argparse

from architecture_model import (
    BUILD_STAGES,
    MODULES,
    SCENARIOS,
    ArchitectureState,
    admit_candidate,
    advance_search,
    complete_judge,
    consult_oracle,
    new_state,
    open_reasoning,
    reach_cutoff,
    validate_static_design,
)


BOLD = "\x1b[1m"
DIM = "\x1b[2m"
RESET = "\x1b[0m"
CLEAR = "\x1b[2J\x1b[H"


def render(state: ArchitectureState, *, clear: bool = True) -> None:
    if clear:
        print(CLEAR, end="")
    print(f"{BOLD}Generalized Solo architecture prototype{RESET}")
    print(f"{DIM}PROTOTYPE — no production solver code{RESET}\n")
    print(f"{BOLD}scenario{RESET}:            {state.scenario}")
    print(f"{BOLD}phase{RESET}:               {state.phase}")
    print(f"{BOLD}current owner{RESET}:       {state.owner}")
    print(f"{BOLD}oracle mode/result{RESET}:  {state.oracle_mode} / {state.oracle_disposition}")
    print(f"{BOLD}artifact touched{RESET}:    {state.artifact_touched}")
    print(f"{BOLD}pending preference{RESET}:  {state.preferred_lane or '-'}")
    print(f"{BOLD}first search lane{RESET}:   {state.first_lane or '-'}")
    print(f"{BOLD}reasoning opened{RESET}:    {state.reasoning_opened}")
    print(f"{BOLD}candidate source{RESET}:    {state.candidate_source or '-'}")
    print(f"{BOLD}admitted / judges{RESET}:   {state.candidates_admitted} / {state.judge_calls}")
    print(f"{BOLD}outcome{RESET}:             {state.outcome or '-'}")

    print(f"\n{BOLD}recent ownership trace{RESET}")
    for item in state.trace[-7:]:
        print(f"  {DIM}{item}{RESET}")

    if state.phase == "startup":
        shortcuts = "[o] consult oracle"
    elif state.phase == "search_unopened":
        shortcuts = "[s] open search  [c] cutoff"
    elif state.phase == "searching":
        shortcuts = "[p] pause  [y] yield  [x] exhaust  [c] cutoff"
    elif state.phase == "candidate_admission":
        shortcuts = "[a] admit  [r] reject locally"
    elif state.phase == "awaiting_judge":
        shortcuts = "[a] accepted  [r] incorrect  [e] infrastructure error"
    else:
        shortcuts = "case stopped"
    print(f"\n{BOLD}{shortcuts}{RESET}")
    print(f"{BOLD}[1-4]{RESET} reset scenario  {BOLD}[q]{RESET} quit")


def reset_for_key(key: str) -> ArchitectureState:
    return new_state(SCENARIOS[int(key) - 1])


def interactive(initial_scenario: str) -> None:
    state = new_state(initial_scenario)
    while True:
        render(state)
        key = input("\n> ").strip().lower()[:1]
        try:
            if key == "q":
                return
            if key in ("1", "2", "3", "4"):
                state = reset_for_key(key)
            elif state.phase == "startup" and key == "o":
                state = consult_oracle(state)
            elif state.phase == "search_unopened" and key == "s":
                state = open_reasoning(state)
            elif state.phase in ("search_unopened", "searching") and key == "c":
                state = reach_cutoff(state)
            elif state.phase == "searching" and key in ("p", "y", "x"):
                result = {"p": "paused", "y": "candidate", "x": "exhausted"}[key]
                state = advance_search(state, result)
            elif state.phase == "candidate_admission" and key in ("a", "r"):
                state = admit_candidate(state, admissible=key == "a")
            elif state.phase == "awaiting_judge" and key in ("a", "r", "e"):
                status = {"a": "accepted", "r": "incorrect", "e": "error"}[key]
                state = complete_judge(state, status)
        except ValueError as error:
            state = ArchitectureState(
                **{**state.__dict__, "trace": state.trace + (f"invalid action: {error}",)}
            )


def print_scenario(name: str, state: ArchitectureState) -> None:
    print(f"\n=== {name} ===")
    render(state, clear=False)


def batch() -> None:
    print("=== Static architecture ===")
    for result in validate_static_design():
        print(f"- {result}")
    print("\nModules:")
    for module in MODULES:
        deps = ", ".join(module.depends_on) or "stdlib only"
        print(f"- {module.name}: {module.interface}; depends on {deps}")
    print("\nBuild sequence:")
    for index, stage in enumerate(BUILD_STAGES, 1):
        print(f"{index}. {stage.name}")

    disabled = open_reasoning(consult_oracle(new_state("disabled")))
    disabled = advance_search(disabled, "candidate")
    disabled = admit_candidate(disabled, admissible=True)
    disabled = complete_judge(disabled, "incorrect")
    print_scenario("Disabled oracle, rejected strategy candidate", disabled)

    cache = consult_oracle(new_state("cache_hit"))
    cache = admit_candidate(cache, admissible=True)
    cache = complete_judge(cache, "accepted")
    print_scenario("Accepted cache candidate without opening reasoning", cache)

    rejected_cache = consult_oracle(new_state("cache_hit"))
    rejected_cache = admit_candidate(rejected_cache, admissible=True)
    rejected_cache = complete_judge(rejected_cache, "incorrect")
    rejected_cache = open_reasoning(rejected_cache)
    print_scenario("Rejected cache clears hint before neutral search", rejected_cache)

    hinted = open_reasoning(consult_oracle(new_state("direction_hint")))
    hinted = reach_cutoff(hinted)
    print_scenario("Direction hint consumed once, then cutoff", hinted)

    invalid = open_reasoning(consult_oracle(new_state("invalid_oracle")))
    print_scenario("Invalid oracle falls through to countermodel-first search", invalid)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batch", action="store_true")
    parser.add_argument("--scenario", choices=SCENARIOS, default="disabled")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.batch:
        batch()
        return
    interactive(args.scenario)


if __name__ == "__main__":
    main()
