/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import WorkerCompromiseProof.RankSum
public import Mathlib.Data.Fin.Tuple.Sort
public import WorkerCompromiseProof.Core.Welfare

/-!
# The exponential moment of the log inverse rank percentile

Averaging over exchangeable firm labels reduces the one-worker estimate to
a sum over sorted ranks. Inclusive ranks only become larger in the presence
of ties, so the estimate holds for these ranks without any tie-breaking.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory ProbabilityTheory Imbalanced
open scoped BigOperators

/-- The exponential weight of a firm's log inverse rank percentile in a worker column. -/
noncomputable def columnRankMoment {n : ℕ} (i : Fin n) (t : ℝ) (y : Fin n → ℝ) : ℝ :=
  Real.exp (t * Real.log ((n : ℝ) / (inclusiveColumnRank i y : ℝ)))

theorem measurable_columnRankMoment {n : ℕ} (i : Fin n) (t : ℝ) :
    Measurable (columnRankMoment i t) :=
  (Measurable.of_discrete (f := fun k : ℕ ↦ Real.exp (t * Real.log ((n : ℝ) / k)))).comp
    (measurable_inclusiveColumnRank i)

theorem one_le_inclusiveColumnRank {n : ℕ} (i : Fin n) (y : Fin n → ℝ) :
    1 ≤ inclusiveColumnRank i y := by
  classical
  unfold inclusiveColumnRank
  simpa only [le_refl, ite_true] using
    (Finset.single_le_sum (f := fun k : Fin n ↦ if y i ≤ y k then (1 : ℕ) else 0)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i))

private theorem moment_antitone {n : ℕ} {t a b : ℝ} (hn : 0 < n) (ht : 0 ≤ t)
    (ha : 0 < a) (hab : a ≤ b) :
    Real.exp (t * Real.log ((n : ℝ) / b)) ≤ Real.exp (t * Real.log ((n : ℝ) / a)) := by
  have hb := ha.trans_le hab
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ ht
  apply Real.log_le_log (div_pos (Nat.cast_pos.mpr hn) hb)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) ha hab

theorem integrable_columnRankMoment {n : ℕ} (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (columnRankMoment i t) (Measure.pi fun _ : Fin n ↦ expMeasure 1) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  apply (integrable_const (Real.exp (t * Real.log ((n : ℝ) / 1)))).mono'
    (measurable_columnRankMoment i t).aestronglyMeasurable
  filter_upwards with y
  rw [Real.norm_eq_abs, columnRankMoment, abs_of_pos (Real.exp_pos _)]
  exact moment_antitone (Nat.zero_lt_of_lt i.isLt) ht zero_lt_one (by
    exact_mod_cast one_le_inclusiveColumnRank i y)

private theorem sum_columnRankMoment_le_grid {n : ℕ} (y : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∑ i, columnRankMoment i t y) ≤
      ∑ j : Fin n, Real.exp (t * Real.log ((n : ℝ) / ((j.val : ℝ) + 1))) := by
  classical
  let e := Tuple.sort (fun i ↦ -y i)
  have he : Antitone (y ∘ e) := fun i j hij ↦
    neg_le_neg_iff.mp (Tuple.monotone_sort (fun k ↦ -y k) hij)
  rw [← Equiv.sum_comp e (fun i ↦ columnRankMoment i t y)]
  apply Finset.sum_le_sum
  intro j _
  have hR : j.val + 1 ≤ inclusiveColumnRank (e j) y := by
    unfold inclusiveColumnRank
    rw [← Equiv.sum_comp e (fun k ↦ if y (e j) ≤ y k then (1 : ℕ) else 0)]
    calc
      j.val + 1 = ∑ _k ∈ Finset.Iic j, (1 : ℕ) := by simp [Fin.card_Iic]
      _ = ∑ k ∈ Finset.Iic j, if y (e j) ≤ y (e k) then 1 else 0 := by
        exact Finset.sum_congr rfl fun k hk ↦ (ite_eq_left (he (Finset.mem_Iic.mp hk))).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ Nat.zero_le _)
  exact moment_antitone (Nat.zero_lt_of_lt j.isLt) ht (by positivity) (by exact_mod_cast hR)

private theorem integral_columnRankMoment_eq {n : ℕ} (i j : Fin n) (t : ℝ) :
    ∫ y, columnRankMoment j t y ∂(Measure.pi fun _ : Fin n ↦ expMeasure 1) =
      ∫ y, columnRankMoment i t y ∂(Measure.pi fun _ : Fin n ↦ expMeasure 1) := by
  classical
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  let e := Equiv.swap i j
  let σ := MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e
  have hp := measurePreserving_piCongrLeft (fun _ : Fin n ↦ expMeasure 1) e
  have hrank (y : Fin n → ℝ) : inclusiveColumnRank j (σ y) = inclusiveColumnRank i y := by
    unfold inclusiveColumnRank
    have heval (k : Fin n) : σ y k = y (e.symm k) := by
      simpa only [σ, e.apply_symm_apply] using
        (MeasurableEquiv.piCongrLeft_apply_apply e (β := fun _ ↦ ℝ) y (e.symm k))
    simp_rw [heval]
    rw [show e.symm j = i by simp [e]]
    exact Equiv.sum_comp e.symm (fun k ↦ if y i ≤ y k then 1 else 0)
  calc
    _ = ∫ y, columnRankMoment j t (σ y) ∂(Measure.pi fun _ : Fin n ↦ expMeasure 1) :=
      (hp.integral_comp' (f := σ) (columnRankMoment j t)).symm
    _ = _ := integral_congr_ae (ae_of_all _ fun y ↦ by simp only [columnRankMoment, hrank])

/-- One firm's inverse-rank moment is bounded by the moment of a continuous uniform percentile. -/
theorem integral_columnRankMoment_le {n : ℕ} (i : Fin n) {t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    (∫ y, columnRankMoment i t y ∂(Measure.pi fun _ : Fin n ↦ expMeasure 1)) ≤ (1 - t)⁻¹ := by
  classical
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  let μ : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n ↦ expMeasure 1
  have hi : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hg (j : Fin n) := integrable_columnRankMoment j ht.le
  apply (mul_le_mul_iff_right₀ hi).mp
  calc
    _ = ∑ j : Fin n, ∫ y, columnRankMoment j t y ∂μ := by
      simp only [μ, integral_columnRankMoment_eq i, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    _ = ∫ y, ∑ j : Fin n, columnRankMoment j t y ∂μ := (integral_finsetSum _ (fun j _ ↦ hg j)).symm
    _ ≤ ∫ _y, ((n : ℝ) * (1 - t)⁻¹) ∂μ :=
      integral_mono (integrable_finsetSum _ (fun j _ ↦ hg j)) (integrable_const _)
        fun y ↦ (sum_columnRankMoment_le_grid y ht.le).trans
          (sum_rankGridMoment_le (Nat.zero_lt_of_lt i.isLt) ht ht')
    _ = _ := by simp [μ]

end WorkerCompromiseProof.Bounds.Paper
