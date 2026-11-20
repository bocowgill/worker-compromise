/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib

/-!
# The vacancy correction and the simplex volume
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- The vacancy factor absorbs all the assigned worker and firm marks on the missing diagonal. -/
theorem vacancyStabilityProduct_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → ℝ) {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1)
    (hy : ∀ i, y i ∈ Icc (0 : ℝ) 1) :
    (∏ i, (1 - q * x i)) *
      (∏ i, ∏ j ∈ Finset.univ.erase i, (1 - q ^ 2 * x i * y j)) ≤
        Real.exp (-(q ^ 2 * (∑ i, x i) * (∑ i, y i))) := by
  have hq2 : q ^ 2 ≤ q := by nlinarith [mul_nonneg hq.1 (sub_nonneg.mpr hq.2)]
  have hxq (i : ι) : q * x i ≤ 1 :=
    (mul_le_of_le_one_left (hx i).1 hq.2).trans (hx i).2
  have hxyq (i j : ι) : q ^ 2 * x i * y j ≤ 1 :=
    (mul_le_of_le_one_left (hy j).1 ((mul_le_mul_of_nonneg_right hq2 (hx i).1).trans (hxq i))).trans (hy j).2
  calc
    _ ≤ (∏ i, Real.exp (-(q * x i))) *
        (∏ i, ∏ j ∈ Finset.univ.erase i, Real.exp (-(q ^ 2 * x i * y j))) := by
      have hleft : (∏ i, (1 - q * x i)) ≤ (∏ i, Real.exp (-(q * x i))) :=
        Finset.prod_le_prod₀ (fun i _ ↦ sub_nonneg.mpr (hxq i))
          (fun i _ ↦ Real.one_sub_le_exp_neg _)
      have hright : (∏ i, ∏ j ∈ Finset.univ.erase i, (1 - q ^ 2 * x i * y j)) ≤
          (∏ i, ∏ j ∈ Finset.univ.erase i, Real.exp (-(q ^ 2 * x i * y j))) := by
        apply Finset.prod_le_prod₀
        · intro i _
          exact Finset.prod_nonneg (fun j _ ↦ sub_nonneg.mpr (hxyq i j))
        · intro i _
          exact Finset.prod_le_prod₀ (fun j _ ↦ sub_nonneg.mpr (hxyq i j))
            (fun _ _ ↦ Real.one_sub_le_exp_neg _)
      exact mul_le_mul hleft hright
        (Finset.prod_nonneg (fun i _ ↦ Finset.prod_nonneg
          (fun j _ ↦ sub_nonneg.mpr (hxyq i j)))) (Finset.prod_nonneg (fun _ _ ↦ Real.exp_nonneg _))
    _ ≤ _ := by
      simp_rw [← Real.exp_sum, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hrow (i : ι) :
          -(q * x i) + ∑ j ∈ Finset.univ.erase i, -(q ^ 2 * x i * y j) ≤
            ∑ j, -(q ^ 2 * x i * y j) := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        have hdiag : q ^ 2 * x i * y i ≤ q * x i := by
          calc
            _ ≤ q ^ 2 * x i * 1 := mul_le_mul_of_nonneg_left (hy i).2 (mul_nonneg (sq_nonneg _) (hx i).1)
            _ ≤ _ := by
              rw [mul_one]
              exact mul_le_mul_of_nonneg_right hq2 (hx i).1
        linarith
      calc
        _ = ∑ i, (-(q * x i) + ∑ j ∈ Finset.univ.erase i, -(q ^ 2 * x i * y j)) :=
          Finset.sum_add_distrib.symm
        _ ≤ ∑ i, ∑ j, -(q ^ 2 * x i * y j) := Finset.sum_le_sum (fun i _ ↦ hrow i)
        _ = _ := by
          simp only [Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

/-- The sum of the assigned worker marks at or above the cutoff. -/
noncomputable def workerTailMass {ι : Type*} [Fintype ι] (b : ℝ) (y : ι → ℝ) : ℝ :=
  ∑ j, if b ≤ y j then y j else 0

@[fun_prop]
theorem measurable_workerTailMass {ι : Type*} [Fintype ι] (b : ℝ) :
    Measurable (workerTailMass b : (ι → ℝ) → ℝ) := by
  unfold workerTailMass
  exact Finset.measurable_sum _ (fun i _ ↦
    Measurable.ite (measurableSet_le measurable_const (measurable_pi_apply i))
      (measurable_pi_apply i) measurable_const)

/-- Product of the no-block probabilities for one vacancy and the off-diagonal pairs. -/
def vacancyStabilityProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℝ) (x y : ι → ℝ) : ℝ :=
  (∏ i, (1 - q * x i)) * (∏ i, ∏ j ∈ Finset.univ.erase i, (1 - q ^ 2 * x i * y j))

private theorem lintegral_Ici_translate {f : ℝ → ℝ≥0∞} (hf : Measurable f) (t : ℝ) :
    (∫⁻ x in Ici (0 : ℝ), f (x + t)) = ∫⁻ z in Ici t, f z := by
  have he : (fun x : ℝ ↦ x + t) ⁻¹' Ici t = Ici 0 := by
    ext x
    simp
  simpa only [he] using
    (measurePreserving_add_right (volume : Measure ℝ) t).setLIntegral_comp_preimage
      (s := Ici t) measurableSet_Ici hf

private theorem lintegral_triangle_swap {f g : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x in Ici (0 : ℝ), ∫⁻ t in Ici (0 : ℝ), g t * f (x + t)) =
      ∫⁻ z in Ici (0 : ℝ), f z * ∫⁻ t in Icc (0 : ℝ) z, g t := by
  let ν : Measure ℝ := volume.restrict (Ici (0 : ℝ))
  have hi : Measurable (fun p : ℝ × ℝ ↦ g p.2 * f (p.1 + p.2)) := by fun_prop
  change (∫⁻ x, ∫⁻ t, g t * f (x + t) ∂ν ∂ν) = _
  rw [lintegral_lintegral_swap (f := fun x t ↦ g t * f (x + t)) hi.aemeasurable]
  have he (t : ℝ) : (∫⁻ x, g t * f (x + t) ∂ν) =
      g t * ∫⁻ z in Ici t, f z := by
    have hft : Measurable (fun x ↦ f (x + t)) := by fun_prop
    rw [lintegral_const_mul _ hft]
    congr 1
    exact lintegral_Ici_translate hf t
  simp_rw [he]
  have he' : ∀ᵐ t ∂ν, g t * (∫⁻ z in Ici t, f z) =
      ∫⁻ z, (if t ≤ z then g t * f z else 0) ∂ν := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ici] with t ht
    have hts : Ici t ⊆ Ici (0 : ℝ) := Ici_subset_Ici.mpr ht
    rw [show (volume : Measure ℝ).restrict (Ici t) = ν.restrict (Ici t) by
        rw [Measure.restrict_restrict measurableSet_Ici, inter_eq_left.mpr hts],
      ← lintegral_const_mul _ hf, ← lintegral_indicator measurableSet_Ici]
    apply lintegral_congr
    intro z
    by_cases hz : t ≤ z <;> simp [hz]
  rw [lintegral_congr_ae he']
  have htri : Measurable (fun p : ℝ × ℝ ↦ if p.1 ≤ p.2 then g p.1 * f p.2 else 0) :=
    Measurable.ite (measurableSet_le measurable_fst measurable_snd) (by fun_prop) measurable_const
  rw [lintegral_lintegral_swap (f := fun t z ↦ if t ≤ z then g t * f z else 0)
    htri.aemeasurable]
  apply lintegral_congr
  intro z
  have hineq : (fun t ↦ if t ≤ z then g t * f z else 0) =
      (Iic z).indicator (fun t ↦ g t * f z) := by
    funext t
    by_cases ht : t ≤ z <;> simp [ht]
  rw [hineq, lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    show Iic z ∩ Ici (0 : ℝ) = Icc 0 z by ext t; simp [and_comm],
    lintegral_mul_const _ hg, mul_comm]

private theorem lintegral_Icc_pow_div_factorial (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    (∫⁻ t in Icc (0 : ℝ) z, ENNReal.ofReal (t ^ n / (n.factorial : ℝ))) =
      ENNReal.ofReal (z ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
  have hcont : Continuous (fun t : ℝ ↦ t ^ n / (n.factorial : ℝ)) := by fun_prop
  have hi : Integrable (fun t : ℝ ↦ t ^ n / (n.factorial : ℝ))
      ((volume : Measure ℝ).restrict (Icc 0 z)) :=
    hcont.continuousOn.integrableOn_Icc
  have hnn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Icc 0 z)]
      (fun t : ℝ ↦ t ^ n / (n.factorial : ℝ)) := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with t ht
    exact div_nonneg (pow_nonneg ht.1 _) (Nat.cast_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hz,
    intervalIntegral.integral_div, integral_pow, zero_pow (Nat.succ_ne_zero _), sub_zero,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, div_div, mul_comm (↑n + 1 : ℝ)]

/-- Radial density of the coordinate sum on the nonnegative orthant.
It follows by induction from a translated one-dimensional integral and Tonelli's theorem. -/
theorem lintegral_orthant_sum {f : ℝ → ℝ≥0∞} (hf : Measurable f) (n : ℕ) :
    (∫⁻ x : Fin (n + 1) → ℝ, f (∑ i, x i)
      ∂(Measure.pi (fun _ : Fin (n + 1) ↦ volume.restrict (Ici (0 : ℝ))))) =
      ∫⁻ z in Ici (0 : ℝ), ENNReal.ofReal (z ^ n / (n.factorial : ℝ)) * f z := by
  let ν : Measure ℝ := volume.restrict (Ici (0 : ℝ))
  induction n generalizing f with
  | zero =>
    have he := (measurePreserving_piUnique (fun _ : Fin 1 ↦ ν)).lintegral_comp hf
    simpa [Fin.sum_univ_one, MeasurableEquiv.piUnique, ν] using he
  | succ n ih =>
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) ↦ ℝ) 0).symm
    have he := ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 2) ↦ ν) 0).symm)
    change MeasurePreserving e (ν.prod (Measure.pi (fun _ : Fin (n + 1) ↦ ν)))
      (Measure.pi (fun _ : Fin (n + 2) ↦ ν)) at he
    change (∫⁻ y : Fin (n + 2) → ℝ, f (∑ i, y i) ∂(Measure.pi fun _ ↦ ν)) = _
    rw [← he.lintegral_comp_emb e.measurableEmbedding]
    have hsum (p : ℝ × (Fin (n + 1) → ℝ)) : (∑ i, e p i) = p.1 + ∑ j, p.2 j := by
      simp [Fin.sum_univ_succ, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv]
    simp_rw [hsum]
    rw [lintegral_prod _ (by fun_prop)]
    have hinner (x : ℝ) := ih (f := fun t ↦ f (x + t))
      (hf.comp (measurable_const.add measurable_id))
    change (∫⁻ x, ∫⁻ v : Fin (n + 1) → ℝ, f (x + ∑ j, v j)
      ∂(Measure.pi (fun _ ↦ ν)) ∂ν) = _
    calc
      _ = ∫⁻ x in Ici (0 : ℝ), ∫⁻ t in Ici (0 : ℝ),
          ENNReal.ofReal (t ^ n / (n.factorial : ℝ)) * f (x + t) :=
        lintegral_congr hinner
      _ = ∫⁻ z in Ici (0 : ℝ), f z * ∫⁻ t in Icc (0 : ℝ) z,
          ENNReal.ofReal (t ^ n / (n.factorial : ℝ)) :=
        lintegral_triangle_swap hf (by fun_prop)
      _ = _ := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ici] with z hz
        rw [lintegral_Icc_pow_div_factorial n hz, mul_comm]

private theorem pi_restrict_Icc_le_pi_restrict_Ici {ι : Type*} [Fintype ι] :
    Measure.pi (fun _ : ι ↦ volume.restrict (Icc (0 : ℝ) 1)) ≤
      Measure.pi (fun _ : ι ↦ volume.restrict (Ici (0 : ℝ))) := by
  simp_rw [← Measure.restrict_pi_pi, ← volume_pi]
  apply Measure.restrict_mono _ le_rfl
  intro _ h i hi
  exact (h i hi).1

/-- The logarithmic integral from the firm marks on the part of the cube with sum at least s. -/
theorem markCube_lintegral_inv_sum_pow_le (n : ℕ) {s : ℝ} (hs : 0 < s) (hsn : s ≤ n + 1) :
    (∫⁻ x : Fin (n + 1) → ℝ in {x | s ≤ (∑ i, x i)},
      ENNReal.ofReal (((∑ i, x i) : ℝ)⁻¹ ^ (n + 1))
      ∂(Measure.pi (fun _ : Fin (n + 1) ↦ volume.restrict (Icc (0 : ℝ) 1)))) ≤
        ENNReal.ofReal (Real.log ((n + 1) / s) / (n.factorial : ℝ)) := by
  let μ : Measure (Fin (n + 1) → ℝ) :=
    Measure.pi (fun _ : Fin (n + 1) ↦ volume.restrict (Icc (0 : ℝ) 1))
  let ν : Measure (Fin (n + 1) → ℝ) :=
    Measure.pi (fun _ : Fin (n + 1) ↦ volume.restrict (Ici (0 : ℝ)))
  let f : ℝ → ℝ≥0∞ := (Icc s (n + 1 : ℝ)).indicator
    (fun z ↦ ENNReal.ofReal (z⁻¹ ^ (n + 1)))
  have hf : Measurable f := Measurable.indicator (by fun_prop) measurableSet_Icc
  have hsum : ∀ᵐ x ∂μ, (∑ i, x i) ≤ (n : ℝ) + 1 := by
    have hμ : μ = (volume : Measure (Fin (n + 1) → ℝ)).restrict
        (Set.univ.pi (fun _ : Fin (n + 1) ↦ Icc (0 : ℝ) 1)) := by
      rw [volume_pi, Measure.restrict_pi_pi]
    rw [hμ]
    filter_upwards [ae_restrict_mem (μ := (volume : Measure (Fin (n + 1) → ℝ)))
      (MeasurableSet.univ_pi fun _ : Fin (n + 1) ↦ measurableSet_Icc)] with x hx
    calc
      _ ≤ ∑ _i : Fin (n + 1), (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ ↦ (Set.mem_univ_pi.mp hx i).2)
      _ = _ := by simp
  have hE : MeasurableSet {x : Fin (n + 1) → ℝ | s ≤ (∑ i, x i)} :=
    measurableSet_le measurable_const (by fun_prop)
  calc
    _ = ∫⁻ x : Fin (n + 1) → ℝ, f (∑ i, x i) ∂μ := by
      rw [← lintegral_indicator hE]
      apply lintegral_congr_ae
      filter_upwards [hsum] with x hx
      by_cases hsx : s ≤ (∑ i, x i) <;> simp [f, hsx, hx]
    _ ≤ ∫⁻ x : Fin (n + 1) → ℝ, f (∑ i, x i) ∂ν :=
      lintegral_mono' pi_restrict_Icc_le_pi_restrict_Ici le_rfl
    _ = ∫⁻ z in Ici (0 : ℝ), ENNReal.ofReal (z ^ n / (n.factorial : ℝ)) * f z :=
      lintegral_orthant_sum hf n
    _ = ∫⁻ z in Icc s (n + 1 : ℝ), ENNReal.ofReal (z⁻¹ / (n.factorial : ℝ)) := by
      have hi (z : ℝ) : ENNReal.ofReal (z ^ n / (n.factorial : ℝ)) * f z =
          (Icc s (n + 1 : ℝ)).indicator (fun z ↦
            ENNReal.ofReal (z ^ n / (n.factorial : ℝ)) * ENNReal.ofReal (z⁻¹ ^ (n + 1))) z := by
        by_cases hz : z ∈ Icc s (n + 1 : ℝ)
        · simp [f, indicator_of_mem hz]
        · simp [f, indicator_of_notMem hz]
      simp_rw [hi]
      have hs' : Icc s (n + 1 : ℝ) ⊆ Ici (0 : ℝ) := by
        intro z hz
        exact hs.le.trans hz.1
      rw [lintegral_indicator measurableSet_Icc,
        Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hs']
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with z hz
      have hz' := hs.trans_le hz.1
      rw [← ENNReal.ofReal_mul (div_nonneg (pow_nonneg hz'.le _) (Nat.cast_nonneg _))]
      congr 1
      rw [pow_succ, show z ^ n / (n.factorial : ℝ) * (z⁻¹ ^ n * z⁻¹) =
          (z ^ n * z⁻¹ ^ n) * (z⁻¹ / (n.factorial : ℝ)) by ring,
        ← mul_pow, mul_inv_cancel₀ hz'.ne', one_pow, one_mul]
    _ = _ := by
      have hcont : ContinuousOn (fun z : ℝ ↦ z⁻¹ / (n.factorial : ℝ)) (Icc s (n + 1)) :=
        (continuousOn_id.inv₀ (fun z hz ↦ (hs.trans_le hz.1).ne')).div_const _
      have hnn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Icc s (n + 1))]
          (fun z : ℝ ↦ z⁻¹ / (n.factorial : ℝ)) := by
        filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with z hz
        exact div_nonneg (inv_nonneg.mpr (hs.le.trans hz.1)) (Nat.cast_nonneg _)
      rw [← ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc hnn,
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hsn,
        intervalIntegral.integral_div]
      simp only [← one_div, integral_one_div_of_pos hs (hs.trans_le hsn)]

end WorkerCompromiseProof.Bounds
