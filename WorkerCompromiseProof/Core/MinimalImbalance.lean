/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib
public import WorkerCompromiseProof.Core.SwitchingCostMatching
public import WorkerCompromiseProof.Core.WelfareOptima

/-!
# The normalized ordinal compromise
-/

@[expose] public section

namespace WorkerCompromiseProof.Imbalanced

open Filter MeasureTheory SwitchingCostMatching
open scoped Topology

/-- The logarithmic exponent of the best ordinal welfare compromise. -/
noncomputable def ordinalCompromiseExponent {n w : ℕ} (p : Profile n w) (ε : ℝ) : ℝ :=
  Real.log (bestRankCompromise p ε) / Real.log n

/-- The logarithmic normalization is positive at market sizes at least two. -/
theorem log_firmCount_pos {n : ℕ} (hn : 2 ≤ n) : 0 < Real.log (n : ℝ) :=
  Real.log_pos (by exact_mod_cast (show 1 < n by omega))

end WorkerCompromiseProof.Imbalanced
