/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib
public import WorkerCompromiseProof.Core.SwitchingCostMatching
public import WorkerCompromiseProof.Core.ImbalancedExistence

/-!
# Ranks and utilities for injective matchings

Worker ranks are averaged over matched workers. Worker cardinal utility is averaged over
the entire worker population, with utility zero for each unmatched worker.
All definitions reuse `SwitchingCostMatching.Profile`, `Matching`, and `IsStable`.
-/

@[expose] public section

namespace WorkerCompromiseProof.Imbalanced

open MeasureTheory SwitchingCostMatching
open scoped BigOperators

open scoped Classical in
/-- The finite set of injections stable at the given switching cost. -/
noncomputable def stableMatchings {n w : ℕ} (p : Profile n w) (ε : ℝ) :
    Finset (Matching n w) :=
  Finset.univ.filter fun m ↦ IsStable p ε m

@[simp]
theorem mem_stableMatchings {n w : ℕ} (p : Profile n w) (ε : ℝ) (m : Matching n w) :
    m ∈ stableMatchings p ε ↔ IsStable p ε m := by
  classical
  simp [stableMatchings]

/-- The stable set is nonempty when there are more workers and the cost is nonnegative. -/
theorem stableMatchings_nonempty {n w : ℕ} (p : Profile n w) (hcard : n < w)
    {ε : ℝ} (hε : 0 ≤ ε) : (stableMatchings p ε).Nonempty := by
  obtain ⟨m, hm⟩ := exists_isStable p hcard hε
  exact ⟨m, (mem_stableMatchings p ε m).mpr hm⟩

open scoped Classical in
/-- Firm total rank among all workers, including the assigned worker in each rank. -/
noncomputable def firmRankSum {n w : ℕ} (p : Profile n w) (m : Matching n w) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin w, if p (false, i, m i) ≤ p (false, i, j) then 1 else 0

open scoped Classical in
/-- Total rank over matched workers. Each matched worker `m i` ranks all firms. -/
noncomputable def matchedWorkerRankSum {n w : ℕ} (p : Profile n w) (m : Matching n w) : ℕ :=
  ∑ i : Fin n, ∑ k : Fin n, if p (true, i, m i) ≤ p (true, k, m i) then 1 else 0

open scoped Classical in
/-- Assigned utility of worker `j`, with zero for an unmatched worker. -/
noncomputable def workerRealizedUtility {n w : ℕ} (p : Profile n w) (m : Matching n w)
    (j : Fin w) : ℝ :=
  ∑ i : Fin n, if m i = j then p (true, i, j) else 0

/-- Total worker utility is the sum over assigned pairs; unmatched workers contribute zero. -/
theorem sum_workerRealizedUtility {n w : ℕ} (p : Profile n w) (m : Matching n w) :
    ∑ j, workerRealizedUtility p m j = ∑ i, p (true, i, m i) := by
  classical
  unfold workerRealizedUtility
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- Firm average rank over the `n` firms. -/
noncomputable def firmAverageRank {n w : ℕ} (p : Profile n w) (m : Matching n w) : ℝ :=
  (firmRankSum p m : ℝ) / n

/-- Worker average rank over the `n` matched workers. -/
noncomputable def matchedWorkerAverageRank {n w : ℕ} (p : Profile n w)
    (m : Matching n w) : ℝ :=
  (matchedWorkerRankSum p m : ℝ) / n

/-- Mean assigned firm utility over all firms. -/
noncomputable def firmAverageUtility {n w : ℕ} (p : Profile n w) (m : Matching n w) : ℝ :=
  (∑ i : Fin n, p (false, i, m i)) / n

/-- Mean worker utility over all `w` workers, including unmatched workers at utility zero. -/
noncomputable def workerAverageUtility {n w : ℕ} (p : Profile n w) (m : Matching n w) : ℝ :=
  (∑ j : Fin w, workerRealizedUtility p m j) / w

theorem workerAverageUtility_eq_sum {n w : ℕ} (p : Profile n w) (m : Matching n w) :
    workerAverageUtility p m = (∑ i : Fin n, p (true, i, m i)) / w := by
  unfold workerAverageUtility
  rw [sum_workerRealizedUtility]

/-- The larger of the two sides' average ranks, with worker ranks over matched workers. -/
noncomputable def rankCompromise {n w : ℕ} (p : Profile n w) (m : Matching n w) : ℝ :=
  max (firmAverageRank p m) (matchedWorkerAverageRank p m)

/-- The smaller of the two population-average utilities, normalized by $\log n$. -/
noncomputable def utilityCompromise {n w : ℕ} (p : Profile n w) (m : Matching n w) : ℝ :=
  min (firmAverageUtility p m / Real.log n) (workerAverageUtility p m / Real.log n)

/-- Every matched worker counts its assigned firm in its rank. -/
theorem le_matchedWorkerRankSum {n w : ℕ} (p : Profile n w) (m : Matching n w) :
    n ≤ matchedWorkerRankSum p m := by
  classical
  unfold matchedWorkerRankSum
  calc
    n = ∑ _i : Fin n, 1 := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        1 = if p (true, i, m i) ≤ p (true, i, m i) then 1 else 0 := by simp
        _ ≤ _ := Finset.single_le_sum
          (f := fun k : Fin n ↦
            if p (true, i, m i) ≤ p (true, k, m i) then (1 : ℕ) else 0)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)

theorem one_le_matchedWorkerAverageRank {n w : ℕ} (p : Profile n w) (m : Matching n w)
    (hn : 0 < n) : 1 ≤ matchedWorkerAverageRank p m := by
  unfold matchedWorkerAverageRank
  rw [le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)]
  simpa using (Nat.cast_le.mpr (le_matchedWorkerRankSum p m) :
    (n : ℝ) ≤ matchedWorkerRankSum p m)

theorem measurableSet_isStable (n w : ℕ) (ε : ℝ) (m : Matching n w) :
    MeasurableSet {p : Profile n w | IsStable p ε m} := by
  apply Measurable.setOf
  unfold IsStable IsBlockingPair
  fun_prop (disch := exact measurable_pi_apply _)

theorem measurable_matchedWorkerRankSum (n w : ℕ) (m : Matching n w) :
    Measurable (fun p : Profile n w ↦ matchedWorkerRankSum p m) := by
  classical
  unfold matchedWorkerRankSum
  exact Finset.measurable_fun_sum _ fun i _ ↦ Finset.measurable_fun_sum _ fun k _ ↦
    Measurable.ite (measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _))
      measurable_const measurable_const

end WorkerCompromiseProof.Imbalanced
