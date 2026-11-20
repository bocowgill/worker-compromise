/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import WorkerCompromiseProof.Scores
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The two worker welfare bounds from a joint payoff bound

The concavity of the logarithm connects the firm tail sum to high mean firm utility.
The same inequality compares the log inverse of the mean worker rank with the mean
log inverse rank. Thus either good worker outcome would violate the joint payoff bound.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open SwitchingCostMatching Imbalanced
open scoped BigOperators

private theorem mean_log_le_log_mean {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) :
    (∑ i, Real.log (x i)) / n ≤ Real.log ((∑ i, x i) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : ∑ _i : Fin n, (n : ℝ)⁻¹ = 1 := by simp [hn'.ne']
  have h := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := Finset.univ) (p := x) (w := fun _ ↦ (n : ℝ)⁻¹)
    (fun _ _ ↦ (inv_pos.mpr hn').le) hw (fun i _ ↦ hx i)
  simpa only [smul_eq_mul, ← Finset.mul_sum, div_eq_inv_mul] using h

/-- An upper bound on the firm tail sum implies a lower bound on mean firm utility. -/
theorem firmMean_ge_of_score_le {n w : ℕ} (hn : 0 < n) (p : Profile n w)
    (m : Matching n w) {δ : ℝ}
    (hS : compromiseFirmScore p m ≤ (n : ℝ) ^ (1 / 2 - 2 * δ)) :
    (1 / 2 + 2 * δ) * Real.log n ≤ firmAverageUtility p m := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let x (i : Fin n) := Real.exp (-p (false, i, m i))
  have hpos : 0 < ∑ i, x i :=
    Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty
  have hj := mean_log_le_log_mean hn x (fun i ↦ Real.exp_pos _)
  have hlog := Real.log_le_log hpos hS
  rw [Real.log_rpow hn'] at hlog
  rw [Real.log_div hpos.ne' hn'.ne'] at hj
  change Real.log (∑ i, x i) ≤ _ at hlog
  simp only [x, Real.log_exp, Finset.sum_neg_distrib, neg_div] at hj
  unfold firmAverageUtility
  dsimp only [x] at hlog
  linarith

/-- The mean log inverse rank bounds the log inverse of the mean rank from above. -/
private theorem log_inv_mean_rank_le {n : ℕ} (hn : 0 < n) (R : Fin n → ℝ)
    (hR : ∀ i, 0 < R i) :
    Real.log n - Real.log ((∑ i, R i) / n) ≤ (∑ i, Real.log (n / R i)) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hj := mean_log_le_log_mean hn R hR
  rw [show (∑ i, Real.log (n / R i)) = n * Real.log n - ∑ i, Real.log (R i) by
    simp [Real.log_div hn'.ne' (hR _).ne', Finset.sum_sub_distrib]]
  rw [sub_div, mul_div_cancel_left₀ _ hn'.ne']
  linarith

/-- The paper's deterministic implication. The sum in the second hypothesis may be
bounded on the whole market before the matching is selected. -/
theorem welfare_of_cutoffs {n w : ℕ} (hn : 0 < n) (p : Profile n w)
    (m : Matching n w) {δ : ℝ}
    (hS : compromiseFirmScore p m ≤ (n : ℝ) ^ (1 / 2 - 2 * δ))
    (hcap : (∑ i, (p (false, i, m i) + workerScore p i (m i))) / n <
      (1 + δ) * Real.log n) :
    (n : ℝ) ^ (1 / 2 + δ) < matchedWorkerAverageRank p m ∧
      matchedWorkerMeanUtility p m < (1 / 2 - δ) * Real.log n := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hfirm := firmMean_ge_of_score_le hn p m hS
  rw [Finset.sum_add_distrib, add_div] at hcap
  unfold firmAverageUtility at hfirm
  have hworker : (∑ i, workerScore p i (m i)) / n < (1 / 2 - δ) * Real.log n := by
    linarith
  let R (i : Fin n) : ℝ := edgeRank p i (m i)
  have hR (i : Fin n) : 0 < R i := by
    change 0 < (↑(∑ k, if p (true, i, m i) ≤ p (true, k, m i) then 1 else 0 : ℕ) : ℝ)
    exact_mod_cast Finset.sum_pos' (fun _ _ ↦ Nat.zero_le _)
      ⟨i, Finset.mem_univ _, by simp⟩
  have hrank : matchedWorkerAverageRank p m = (∑ i, R i) / n := by
    simp [matchedWorkerAverageRank, matchedWorkerRankSum, R, edgeRank, inclusiveColumnRank]
  constructor
  · have hrel := log_inv_mean_rank_le hn R hR
    rw [← hrank] at hrel
    have hscore : (∑ i, Real.log (n / R i)) / n ≤ (∑ i, workerScore p i (m i)) / n :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ ↦ le_max_right _ _)) hn'.le
    apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hn' _)
      (zero_lt_one.trans_le (one_le_matchedWorkerAverageRank p m hn))).mp
    rw [Real.log_rpow hn']
    linarith
  · exact (div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun i _ ↦ le_max_left (p (true, i, m i)) _)) hn'.le).trans_lt hworker

end WorkerCompromiseProof.Bounds.Paper
