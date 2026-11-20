/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib
public import WorkerCompromiseProof.Core.SwitchingCostMatching
public import WorkerCompromiseProof.Core.ImbalancedModel

/-!
# Welfare optima over the finite stable set

The ordinal objective minimizes the larger average rank. The cardinal objective maximizes
the smaller normalized population-average utility. Both optima are attained when there
are more workers than firms and switching costs are nonnegative.
-/

@[expose] public section

namespace WorkerCompromiseProof.Imbalanced

open MeasureTheory SwitchingCostMatching

open scoped Classical in
/-- The best ordinal compromise. The value is one if the stable set is empty. -/
noncomputable def bestRankCompromise {n w : ℕ} (p : Profile n w) (ε : ℝ) : ℝ :=
  if hs : (stableMatchings p ε).Nonempty then
    ((stableMatchings p ε).image (rankCompromise p)).min' (hs.image _)
  else 1

open scoped Classical in
/-- The best cardinal compromise. The value is zero if the stable set is empty. -/
noncomputable def bestUtilityCompromise {n w : ℕ} (p : Profile n w) (ε : ℝ) : ℝ :=
  if hs : (stableMatchings p ε).Nonempty then
    ((stableMatchings p ε).image (utilityCompromise p)).max' (hs.image _)
  else 0

/-- A stable injection attains the ordinal optimum. -/
theorem bestRankCompromise_attained {n w : ℕ} (p : Profile n w) (hcard : n < w)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ m : Matching n w, IsStable p ε m ∧ bestRankCompromise p ε = rankCompromise p m := by
  classical
  have hs := stableMatchings_nonempty p hcard hε
  obtain ⟨m, hm, he⟩ := Finset.mem_image.mp
    (Finset.min'_mem ((stableMatchings p ε).image (rankCompromise p)) (hs.image _))
  refine ⟨m, (mem_stableMatchings p ε m).mp hm, ?_⟩
  simpa only [bestRankCompromise, dite_eq_left hs] using he.symm

/-- A stable injection attains the cardinal optimum. -/
theorem bestUtilityCompromise_attained {n w : ℕ} (p : Profile n w) (hcard : n < w)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ m : Matching n w, IsStable p ε m ∧ bestUtilityCompromise p ε = utilityCompromise p m := by
  classical
  have hs := stableMatchings_nonempty p hcard hε
  obtain ⟨m, hm, he⟩ := Finset.mem_image.mp
    (Finset.max'_mem ((stableMatchings p ε).image (utilityCompromise p)) (hs.image _))
  refine ⟨m, (mem_stableMatchings p ε m).mp hm, ?_⟩
  simpa only [bestUtilityCompromise, dite_eq_left hs] using he.symm

end WorkerCompromiseProof.Imbalanced
