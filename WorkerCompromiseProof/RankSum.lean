/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.MeanInequalities

/-!
# A moment bound for the uniform rank grid

Weighted arithmetic–geometric mean bounds each inverse percentile by a difference
of consecutive powers. Summing these differences controls the endpoint at rank one.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

private theorem rank_power_step (k : ℕ) {t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    (1 - t) / ((k : ℝ) + 1) ^ t ≤
    ((k : ℝ) + 1) ^ (1 - t) - (k : ℝ) ^ (1 - t) := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hg := Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.mpr ht'.le) ht.le
    (Nat.cast_nonneg k) hk.le (by ring)
  rw [Real.rpow_sub hk, Real.rpow_one]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hk _)).mpr
  rw [sub_mul, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hk _).ne']
  linarith

/-- The mean of the negative percentile moment on the discrete uniform rank grid
is at most the corresponding moment on the unit interval. -/
theorem sum_rankGridMoment_le {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    (∑ j : Fin n, Real.exp (t * Real.log ((n : ℝ) / ((j.val : ℝ) + 1)))) ≤
      (n : ℝ) * (1 - t)⁻¹ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let f (k : ℕ) := (k : ℝ) ^ (1 - t)
  have hsum : (∑ j ∈ Finset.range n, (1-t) / ((j : ℝ) + 1)^t) ≤ f n := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, (f (j+1) - f j) := by
        apply Finset.sum_le_sum
        intro j _
        simpa [f, Nat.cast_add, Nat.cast_one] using rank_power_step j ht ht'
      _ = f n := by rw [Finset.sum_range_sub]; simp [f, Real.zero_rpow (sub_ne_zero.mpr ht'.ne')]
  have hfactor (j : ℕ) :
      Real.exp (t * Real.log ((n : ℝ) / ((j : ℝ) + 1))) =
      ((n : ℝ)^t / (1-t)) * ((1-t) / ((j : ℝ)+1)^t) := by
    have hj : (0 : ℝ) < j + 1 := by positivity
    rw [mul_comm t _, ← Real.rpow_def_of_pos (div_pos hn' hj),
      Real.div_rpow hn'.le hj.le]
    field_simp [sub_ne_zero.mpr ht'.ne']
  change (∑ j : Fin n, (fun k : ℕ ↦ Real.exp (t * Real.log ((n : ℝ) / ((k : ℝ) + 1)))) j.val) ≤ _
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ Real.exp (t * Real.log ((n : ℝ) / ((k : ℝ) + 1)))) n]
  simp_rw [hfactor]
  rw [← Finset.mul_sum]
  calc
    _ ≤ ((n : ℝ)^t / (1-t)) * f n :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg (Real.rpow_nonneg hn'.le _) (sub_nonneg.mpr ht'.le))
    _ = _ := by
      dsimp [f]
      rw [Real.rpow_sub hn', Real.rpow_one]
      field_simp [sub_ne_zero.mpr ht'.ne', (Real.rpow_pos_of_pos hn' t).ne']

end WorkerCompromiseProof.Bounds.Paper
