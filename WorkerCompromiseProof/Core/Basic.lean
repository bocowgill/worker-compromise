/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib
public import WorkerCompromiseProof.Core.SwitchingCostMatching
public import WorkerCompromiseProof.Core.Model

/-!
# Nonnegativity of the switching cost
-/

@[expose] public section

namespace WorkerCompromiseProof

open SwitchingCostMatching
open scoped BigOperators

variable {n : ℕ} (p : Profile n n) (ε t : ℝ)

theorem switchingCost_nonneg (hn : 2 ≤ n) : 0 ≤ switchingCost n := by
  unfold switchingCost
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

end WorkerCompromiseProof
