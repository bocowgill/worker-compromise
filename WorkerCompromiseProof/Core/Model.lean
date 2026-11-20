/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib
public import WorkerCompromiseProof.Core.SwitchingCostMatching

/-!
# The switching cost sequence
-/

@[expose] public section

namespace WorkerCompromiseProof

open SwitchingCostMatching
open scoped BigOperators

/-- The fixed cost sequence $\varepsilon_n = \log n/(6\sqrt n)$. -/
noncomputable def switchingCost (n : ℕ) : ℝ :=
  Real.log n / (6 * Real.sqrt n)

end WorkerCompromiseProof
