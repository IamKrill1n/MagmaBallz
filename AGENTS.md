# Repository Guidelines

## Project Structure & Module Organization

This repository is organized as follows:

```
.
├── README.md                        # Entry point, competition docs
├── docs/                            # Track specifications
│   ├── solo_mode.md                 # Solo track: I/O contract, budgets
│   ├── marathon_mode.md             # Marathon track: compression, file I/O
│   └── agents/                      # Agent-specific documentation
│       ├── issue-tracker.md         # Local issue tracker conventions
│       ├── triage-labels.md         # Default triage labels
│       └── domain.md                # Single-context repo config
├── judge/                           # Deterministic Lean verifier
│   ├── verify.py                    # Core verification logic
│   ├── challenger.py                # Adversarial test runner
│   ├── JudgeMagma/Magma.lean        # `◇` operator + Magma class
│   ├── JudgeDecide/DecideBang.lean  # `decideFin!` tactic
│   ├── JudgeFinOp/MemoFinOp.lean    # `finOpTable` helper
│   └── JudgeSupport/Inspect.lean    # Dependency tracking metaprogram
├── pipeline/                        # Evaluation orchestration
│   ├── proxy.py                     # Solo: solver launcher, stdin/stdout mediator
│   ├── runner.py                    # Solo: batch evaluation entry point
│   ├── marathon_runner.py           # Marathon: budget watchdog
│   ├── marathon_proxy.py            # Marathon: local HTTP proxy
│   ├── marathon_score.py            # Marathon: result parser
│   ├── marathon_llm.py              # Marathon: LLM helper
│   └── config.json                  # Budgets + LLM parameters
├── examples/                        # Demo submissions + sample problems
│   ├── problems/                    # Sample sets (normal, hard1-3)
│   ├── solo/                        # Solo demos + tutorial
│   └── marathon/                    # Marathon demos + tutorial
├── tests/                           # Test data (manifests, fixtures)
├── scripts/                         # Helper scripts
│   ├── setup.sh                     # One-command environment setup
│   ├── run_harness.py               # Solo harness (canonical green gate)
│   └── run_marathon_harness.py      # Marathon harness
├── lakefile.lean                    # Lean lake package config
└── CONTRIBUTING.md                  # Contribution guidelines (issue-first)
```

## Build, Test, and Development Commands

### Environment Setup
```bash
# One-command setup (installs Lean, fetches Mathlib, builds judge modules)
bash scripts/setup.sh

# Install Python dependencies
pip install openai

# Activate the environment
source .env.judge
```

### Run Tests
```bash
# Solo harness (canonical completion gate; 0 exit = all green)
python3 scripts/run_harness.py

# Marathon harness
python3 scripts/run_marathon_harness.py
```

### Run Demo Solvers
```bash
# Solo demo on sample problems
python3 -m pipeline.runner \
  --submission examples/solo/demos/baseline \
  --problems examples/problems/sample_20.json

# Marathon demo
python3 scripts/run_marathon.py \
  --solver examples/marathon/demos/baseline \
  --manifest tests/marathon_fixtures/manifests/normal_5.jsonl
```

## Coding Style & Naming Conventions

### Lean
- Follow Mathlib conventions
- 2-space indentation
- Prefer `def` over `theorem` for non-propositional definitions
- Use `abbrev` for type synonyms that should unify definitionally

### Python
- Follow PEP 8
- 4-space indentation
- Use type hints for all function signatures
- Prefer `snake_case` for functions and variables
- Use `black` for auto-formatting (if installed)

## Testing Guidelines

- The canonical completion gate is `python3 scripts/run_harness.py`
- Every fix requires a regression test
- Add test fixtures to `tests/fixtures/` or `tests/challenger/`
- Append to the appropriate manifest (`tests/harness_manifest.json` or `tests/challenger_manifest.json`)
- Determinism is required: no randomness or time-dependent logic in tests

## Agent-Specific Instructions

### Issue tracker
Issues and specs live as markdown files in `.scratch/`. See `docs/agents/issue-tracker.md`.

### Triage labels
Uses the default triage labels: needs-triage, needs-info, ready-for-agent, ready-for-human, wontfix. See `docs/agents/triage-labels.md`.

### Domain docs
Single-context repo (one CONTEXT.md + docs/adr/ at repo root). See `docs/agents/domain.md`.
