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

