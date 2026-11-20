/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib
public import WorkerCompromiseProof.Core.SwitchingCostMatching
public import WorkerCompromiseProof.Core.Basic
public import WorkerCompromiseProof.Core.ImbalancedModel
public import WorkerCompromiseProof.Core.MinimalImbalance
public import WorkerCompromiseProof.Core.Model
public import WorkerCompromiseProof.Core.WelfareOptima

/-!
# Failure events and their implications for the welfare optima
-/

@[expose] public section

namespace WorkerCompromiseProof.Imbalanced

open Filter MeasureTheory SwitchingCostMatching
open scoped BigOperators ENNReal Topology

/-- Mean worker utility over the matched workers only. -/
noncomputable def matchedWorkerMeanUtility {n w : ℕ} (p : Profile n w)
    (m : Matching n w) : ℝ :=
  (∑ i : Fin n, p (true, i, m i)) / n

/-- Some stable injection gives the matched workers average rank at most the cutoff. -/
def compromiseOrdinalFailure (n : ℕ) (δ : ℝ) : Set (Profile n (n + 1)) :=
  {p | ∃ m : Matching n (n + 1), IsStable p (switchingCost n) m ∧
    matchedWorkerAverageRank p m ≤ (n : ℝ) ^ (1 / 2 + δ)}

/-- Some stable injection gives the matched workers mean utility at least the cutoff. -/
def compromiseCardinalFailure (n : ℕ) (δ : ℝ) : Set (Profile n (n + 1)) :=
  {p | ∃ m : Matching n (n + 1), IsStable p (switchingCost n) m ∧
    (1 / 2 - δ) * Real.log n ≤ matchedWorkerMeanUtility p m}

theorem measurableSet_compromiseOrdinalFailure (n : ℕ) (δ : ℝ) :
    MeasurableSet (compromiseOrdinalFailure n δ) := by
  apply Measurable.setOf
  refine Measurable.exists fun m ↦ (measurableSet_isStable n (n + 1) _ m).mem.and ?_
  have hr : Measurable (fun p ↦ matchedWorkerAverageRank p m) :=
    (Measurable.of_discrete (f := fun r : ℕ ↦ (r : ℝ) / n)).comp
      (measurable_matchedWorkerRankSum n (n + 1) m)
  exact (measurableSet_le hr (measurable_const (a := (n : ℝ) ^ (1 / 2 + δ)))).mem

theorem measurableSet_compromiseCardinalFailure (n : ℕ) (δ : ℝ) :
    MeasurableSet (compromiseCardinalFailure n δ) := by
  apply Measurable.setOf
  refine Measurable.exists fun m ↦ (measurableSet_isStable n (n + 1) _ m).mem.and ?_
  have hu : Measurable (fun p ↦ matchedWorkerMeanUtility p m) :=
    (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply (true, i, m i)).div_const _
  exact (measurableSet_le (measurable_const (a := (1 / 2 - δ) * Real.log n)) hu).mem

/-- Excluding low matched-worker ranks forces a positive gap in the ordinal optimum. -/
theorem ordinalCompromiseExponent_gt_of_not_mem_compromiseOrdinalFailure {n : ℕ}
    (hn : 2 ≤ n) {p : Profile n (n + 1)} {δ : ℝ}
    (hp : p ∉ compromiseOrdinalFailure n δ) :
    1 / 2 + δ < ordinalCompromiseExponent p (switchingCost n) := by
  obtain ⟨m, hm, hbest⟩ := bestRankCompromise_attained p (Nat.lt_succ_self n)
    (switchingCost_nonneg hn)
  have hworker : (n : ℝ) ^ (1 / 2 + δ) < matchedWorkerAverageRank p m :=
    lt_of_not_ge fun h ↦ hp ⟨m, hm, h⟩
  have hrank := hworker.trans_le (le_max_right (firmAverageRank p m) _)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold ordinalCompromiseExponent
  apply (lt_div_iff₀ (log_firmCount_pos hn)).2
  rw [← Real.log_rpow hn', hbest]
  exact Real.log_lt_log (Real.rpow_pos_of_pos hn' _) hrank

/-- Excluding high matched-worker utilities bounds the population-average cardinal optimum. -/
theorem bestUtilityCompromise_lt_of_not_mem_compromiseCardinalFailure {n : ℕ}
    (hn : 2 ≤ n) {p : Profile n (n + 1)} {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hp : p ∉ compromiseCardinalFailure n δ) :
    bestUtilityCompromise p (switchingCost n) < 1 / 2 - δ := by
  obtain ⟨m, hm, hbest⟩ := bestUtilityCompromise_attained p (Nat.lt_succ_self n)
    (switchingCost_nonneg hn)
  have hlog := log_firmCount_pos hn
  have hcut : 0 ≤ (1 / 2 - δ) * Real.log n := mul_nonneg (sub_nonneg.mpr hδ) hlog.le
  have hmean : matchedWorkerMeanUtility p m < (1 / 2 - δ) * Real.log n :=
    lt_of_not_ge fun h ↦ hp ⟨m, hm, h⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hw' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [hbest]
  refine (min_le_right _ _).trans_lt ((div_lt_iff₀ hlog).2 ?_)
  rw [workerAverageUtility_eq_sum]
  refine (div_lt_iff₀ hw').2 (((div_lt_iff₀ hn').1 hmean).trans_le ?_)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) hcut

/-- Sum of the firms' assigned exponential tail marks. -/
noncomputable def compromiseFirmScore {n w : ℕ} (p : Profile n w) (m : Matching n w) : ℝ :=
  ∑ i : Fin n, Real.exp (-p (false, i, m i))

/-- Some stable injection has firm score above a prescribed bound. -/
def compromiseLargeScore (n : ℕ) (s : ℝ) : Set (Profile n (n + 1)) :=
  {p | ∃ m : Matching n (n + 1), IsStable p (switchingCost n) m ∧
    s < compromiseFirmScore p m}

open ProbabilityTheory

/-- Rank of firm i in an individual worker's column, counting tied firms. -/
noncomputable def inclusiveColumnRank {n : ℕ} (i : Fin n) (y : Fin n → ℝ) : ℕ := by
  classical
  exact ∑ k : Fin n, if y i ≤ y k then 1 else 0

theorem measurable_inclusiveColumnRank {n : ℕ} (i : Fin n) :
    Measurable (inclusiveColumnRank i) := by
  classical
  unfold inclusiveColumnRank
  exact Finset.measurable_fun_sum _ fun k _ ↦
    Measurable.ite (measurableSet_le (measurable_pi_apply i) (measurable_pi_apply k))
      measurable_const measurable_const

end WorkerCompromiseProof.Imbalanced
