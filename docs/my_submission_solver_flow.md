# `my_submission/solver.py` flow

```mermaid
flowchart TD
    A[Problem and time budget] --> B{Cached certificate accepted?}
    B -- Yes --> Z[Finish]
    B -- No --> C[Parse equations and classify semantics]

    C --> D{Infinite model required?}
    D -- Yes --> I[Symbolic-model collaboration]
    I -- Accepted by Lean judge --> Z
    I -- No accepted certificate --> X[Capability gap]

    D -- No --> E[Cheap countermodel search]
    E -- Accepted by Lean judge --> Z
    E -- No accepted certificate --> F[Focused native proof search]
    F -- Accepted by Lean judge --> Z
    F -- No accepted certificate --> G[LLM-guided tool collaboration]
    G -- Accepted by Lean judge --> Z
    G -- No accepted certificate --> H[Deep proof and model fallback]
    H -- Accepted by Lean judge --> Z
    H -- No accepted certificate --> J[Final LLM recovery]
    J -- Accepted by Lean judge --> Z
    J -- No accepted certificate --> U[Unsolved]
```

The file is a staged certificate searcher: it parses one magma implication, tries increasingly expensive countermodel and proof strategies, asks an LLM to select or propose mechanically checked actions, and stops only when the Lean judge accepts a true or false certificate. Failed attempts feed later stages with diagnostics and remembered candidates.

## `my_submission/marathon/solverV3.py` flow

V3 is a budget-aware batch solver. It prioritizes the manifest, gives each problem a deterministic certificate-search pass, then spends the remaining token and time budget on concurrent LLM-guided recovery for unresolved problems. Every successful path writes either a Lean proof certificate or a finite countermodel certificate for external verification.

```mermaid
flowchart TD
    A[Manifest and budgets] --> B[Prioritize problems]
    B --> C[Allocate per-problem time]
    C --> D[Deterministic certificate search]

    D --> E[Known and cheap proof routes]
    D --> F[Cheap countermodel search]
    D --> G[Deeper proof and model search]
    E --> H{Certificate found?}
    F --> H
    G --> H

    H -- Yes --> I[Write certificate]
    H -- No --> J[Queue unresolved problem]
    J --> K[Concurrent LLM-guided recovery]
    K --> L[Parse and validate candidate]
    L --> M{Usable certificate?}
    M -- Yes --> I
    M -- No --> N[Leave unsolved]

    I --> O[External verifier]
```
