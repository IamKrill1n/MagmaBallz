# Restart runbook (after sleep/reboot/crash)

Durable state: everything under `.scratch/` in this repo (committed), plus
the answer vault at `~/dev/active/MagmaBallz-vault/` (NEVER commit/push it).
The session scratchpad under /private/tmp is DISPOSABLE — nothing needed
for recovery lives there anymore.

To resume work:
1. `source .env.judge` (recreate with `bash scripts/setup.sh` if missing).
2. Harness: `.scratch/engine-day/harness/scoreboard.py` (repo-relative paths;
   stage solvers as `subs/<name>/solver.py` next to it). Results append per
   case, so partial runs are readable; rerun with a new --tag rather than
   resuming a tag.
3. Signature bank: regenerate any time with
   `python3 .scratch/frontier-forge/forge_p1.py` (~2 min, resumable).
4. Prospector/Mapmaker: `forge_p2_sieve.py` / `forge_p3_mapmaker.py`
   (deterministic + seeded; safe to re-run from scratch).
5. Long unattended runs on macOS: prefix with `caffeinate -dims` to prevent
   sleep, e.g. `caffeinate -dims python3 ... &`.
6. Byte-identity battery (`battery.py`) restarts from zero — supplementary
   evidence only, safe to skip.
