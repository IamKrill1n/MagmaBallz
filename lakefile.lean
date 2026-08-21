import Lake
open Lake DSL

package «stage2-judge»

-- Pinned Mathlib revision (bump deliberately via `lake update`).
-- lake-manifest.json is the source of truth for the exact commit.
-- Currently mathlib4 tag v4.32.2, matching `lean-toolchain`.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "905b95818eb32af7874a58b427f50c1711a5e96c"

lean_lib «JudgeMagma» where
  srcDir := "judge"
  roots := #[`JudgeMagma.Magma]

lean_lib «JudgeDecide» where
  srcDir := "judge"
  roots := #[`JudgeDecide.DecideBang]

lean_lib «JudgeFinOp» where
  srcDir := "judge"
  roots := #[`JudgeFinOp.MemoFinOp]

lean_lib «JudgeSupport» where
  srcDir := "judge"
  roots := #[`JudgeSupport.Inspect]
