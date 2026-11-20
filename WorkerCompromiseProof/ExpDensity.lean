/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Exponential

/-! # The joint density of independent rate-one exponential variables -/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

private theorem one_dimensional_exp_density :
    (volume.restrict (Ici (0 : ℝ))).withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-x))) =
      expMeasure 1 := by
  rw [← withDensity_indicator measurableSet_Ici]
  change volume.withDensity _ = volume.withDensity (exponentialPDF 1)
  congr 1
  funext x
  by_cases hx : 0 ≤ x <;> simp [indicator, hx, exponentialPDF_eq]

/-- Lebesgue measure on the positive orthant, weighted by the exponential of minus the
coordinate sum, is the product of the standard exponential probability measures. -/
theorem orthant_withDensity_exp_neg_sum (ι : Type*) [Fintype ι] :
    (Measure.pi (fun _ : ι ↦ volume.restrict (Ici (0 : ℝ)))).withDensity
      (fun z ↦ ENNReal.ofReal (Real.exp (-(∑ i, z i)))) =
      Measure.pi (fun _ : ι ↦ expMeasure 1) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  let ν : ι → Measure ℝ := fun i ↦ (volume.restrict (Ici (0 : ℝ))).restrict (s i)
  have hint : Integrable (fun x : ℝ ↦ Real.exp (-x)) (volume.restrict (Ici 0)) := by
    apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
    simpa using integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) 0
  have hi (i : ι) : Integrable (fun x : ℝ ↦ Real.exp (-x)) (ν i) := hint.restrict
  have hprod := Integrable.fintype_prod hi
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  change (∫⁻ z : ι → ℝ, ENNReal.ofReal (Real.exp (-(∑ i, z i))) ∂Measure.pi ν) = _
  simp_rw [← Finset.sum_neg_distrib, Real.exp_sum]
  rw [← ofReal_integral_eq_lintegral_ofReal hprod (ae_of_all _ fun _ ↦
    Finset.prod_nonneg fun _ _ ↦ Real.exp_nonneg _),
    integral_fintype_prod_eq_prod (μ := ν) (fun _ (x : ℝ) ↦ Real.exp (-x)), ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦
      integral_nonneg fun _ ↦ Real.exp_nonneg _)]
  apply Finset.prod_congr rfl
  intro i _
  rw [← one_dimensional_exp_density, withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hi i) (ae_of_all _ fun _ ↦ Real.exp_nonneg _)

end WorkerCompromiseProof.Bounds.Paper
