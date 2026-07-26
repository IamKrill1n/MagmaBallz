# Spec: correctness defects found in the Solo demo solvers

Status: ready-for-human

## Context

A survey of `examples/solo/demos/` on 2026-07-26 turned up two defects in shipped
demo solvers. Both were verified empirically — by patching the file and re-running,
not by reading alone. Full write-ups, including the mechanism and the repros, are in
`SOLVER_COMPENDIUM.md` Part II §4 and §5 (originally `SOLVER_ANALYSIS_NOTES.md`).

`examples/solo/demos/` is organizer-owned framework code, and per `CONTRIBUTING.md`
substantive correctness changes there require a filed issue before a PR. These
tickets exist to satisfy that gate. Nothing has been changed in either file.

## Issues

- `issues/01-dufius-trans-link-pair-swapped.md` — a real correctness bug; the most
  natural two-hop proof shape never fires, and reflexive goals can emit an
  unverified certificate.
- `issues/02-eulerv5-near-miss-score-measures-length.md` — hint-quality only; cannot
  produce a wrong certificate.

## Open question for a human

These are demo/tutorial solvers, not judge or pipeline code. Whether upstream wants
fixes at all — versus leaving the demos as-is and documenting the defects as
learning material — is a call for the maintainers, not something to decide from
here. Both tickets are therefore `ready-for-human`, not `ready-for-agent`.
