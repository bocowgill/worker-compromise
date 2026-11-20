/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WorkerCompromiseProof.Core.TailIntegral
public import WorkerCompromiseProof.Core.UniformLaw

/-!
# A clipped exponential moment

After rescaling the worker marks the coordinates are independent unit exponentials.
The exact moment below integrates separately above and below the threshold. Its
product bounds the probability that their total tail mass is large.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

private noncomputable def tailWeight (a z : ℝ) := Real.exp ((if a ≤ z then z else 0) / 2)

private theorem measurable_tailWeight (a : ℝ) : Measurable (tailWeight a) :=
  (Measurable.div_const (Measurable.ite measurableSet_Ici measurable_id measurable_const) 2).exp

/-- The moment of the contribution of one exponential partner mark above cutoff `a`. -/
theorem lintegral_tailWeight (a : ℝ) (ha : 0 ≤ a) :
    (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp ((if a ≤ z then z else 0) / 2)) ∂expMeasure 1) =
      ENNReal.ofReal (1 - Real.exp (-a) + 2 * Real.exp (-a / 2)) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  let : NullSingletonClass (expMeasure 1) := by unfold expMeasure gammaMeasure; infer_instance
  have hlo : (expMeasure 1).real (Iio a) = 1 - Real.exp (-a) := by
    have he : (expMeasure 1) (Iio a) = (expMeasure 1) (Iic a) := measure_congr Iio_ae_eq_Iic
    rw [measureReal_def, he, ← measureReal_def, ← cdf_eq_real, cdf_expMeasure_eq zero_lt_one,
      ite_eq_left ha, one_mul]
  have hA : (∫⁻ z in Iio a, ENNReal.ofReal (tailWeight a z) ∂expMeasure 1) =
      ENNReal.ofReal (1 - Real.exp (-a)) := by
    rw [← hlo, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    calc
      _ = ∫⁻ _ : ℝ in Iio a, (1 : ℝ≥0∞) ∂expMeasure 1 := by
        apply setLIntegral_congr_fun measurableSet_Iio
        intro z hz
        simp [tailWeight, not_le.mpr (mem_Iio.mp hz)]
      _ = _ := by simp
  have hb : (-1/2 : ℝ) < 0 := by norm_num
  have hi : IntegrableOn (fun z : ℝ ↦ Real.exp ((-1/2) * z)) (Ici a) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr (integrableOn_exp_mul_Ioi hb a)
  have hB : (∫⁻ z in Ici a, ENNReal.ofReal (tailWeight a z) ∂expMeasure 1) =
      ENNReal.ofReal (2 * Real.exp (-a / 2)) := by
    change (∫⁻ z in Ici a, ENNReal.ofReal (tailWeight a z)
      ∂volume.withDensity (exponentialPDF 1)) = _
    have hpdf : Measurable (exponentialPDF 1) := (measurable_exponentialPDFReal 1).ennreal_ofReal
    rw [restrict_withDensity measurableSet_Ici, lintegral_withDensity_eq_lintegral_mul _
      hpdf (measurable_tailWeight a).ennreal_ofReal]
    calc
      _ = ∫⁻ z in Ici a, ENNReal.ofReal (Real.exp ((-1/2) * z)) := by
        apply setLIntegral_congr_fun measurableSet_Ici
        intro z hz
        simp only [Pi.mul_apply, exponentialPDF_of_nonneg (ha.trans hz), one_mul, tailWeight,
          ite_eq_left (mem_Ici.mp hz), ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        ring
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ ↦ Real.exp_nonneg _),
          integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi hb]
        congr 1
        ring_nf
  change (∫⁻ z, ENNReal.ofReal (tailWeight a z) ∂expMeasure 1) = _
  rw [← lintegral_add_compl _ (measurableSet_Iio (a := a)), compl_Iio, hA, hB,
    ENNReal.ofReal_add (by linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)] :
      0 ≤ 1 - Real.exp (-a)) (by positivity)]

private theorem integrable_tailWeight (a : ℝ) (ha : 0 ≤ a) :
    Integrable (tailWeight a) (expMeasure 1) := by
  refine ⟨(measurable_tailWeight a).aestronglyMeasurable, ?_⟩
  have hnn : ∀ᵐ z ∂expMeasure 1, 0 ≤ tailWeight a z := ae_of_all _ fun _ ↦ Real.exp_nonneg _
  rw [hasFiniteIntegral_iff_ofReal hnn,
    show (∫⁻ z, ENNReal.ofReal (tailWeight a z) ∂expMeasure 1) = _ from lintegral_tailWeight a ha]
  exact ENNReal.ofReal_lt_top

/-- Markov's inequality applied to the clipped exponential moment of the iid
standard exponential worker scores. -/
theorem measure_exponentialWorkerTail_le {ι : Type*} [Fintype ι] {a d : ℝ} (ha : 0 ≤ a) :
    (Measure.pi (fun _ : ι ↦ expMeasure 1)) {z | d ≤ workerTailMass a z} ≤
      ENNReal.ofReal (Real.exp (-d / 2) * (1 + 2 * Real.exp (-a / 2)) ^ Fintype.card ι) := by
  let μ := Measure.pi (fun _ : ι ↦ expMeasure 1)
  let E : Set (ι → ℝ) := {z | d ≤ workerTailMass a z}
  let G (z : ι → ℝ) : ℝ := Real.exp (-d / 2) * ∏ i, tailWeight a (z i)
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  have hE : MeasurableSet E := measurableSet_le measurable_const (measurable_workerTailMass a)
  have hi : Integrable G μ :=
    (Integrable.fintype_prod (fun _ : ι ↦ integrable_tailWeight a ha)).const_mul _
  have hpos (z : ι → ℝ) : 0 ≤ G z := mul_nonneg (Real.exp_nonneg _)
    (Finset.prod_nonneg fun i _ ↦ Real.exp_nonneg _)
  have hbound (z : ι → ℝ) : E.indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤ ENNReal.ofReal (G z) := by
    by_cases hz : z ∈ E
    · rw [indicator_of_mem hz, show (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) by simp]
      apply ENNReal.ofReal_le_ofReal
      simp only [G, tailWeight, ← Real.exp_sum, ← Real.exp_add, ← Finset.sum_div]
      apply Real.one_le_exp_iff.mpr
      have : d ≤ ∑ i, (if a ≤ z i then z i else 0) := hz
      linarith
    · simp only [indicator_of_notMem hz, zero_le]
  have hmoment : (∫ z, tailWeight a z ∂expMeasure 1) ≤ 1 + 2 * Real.exp (-a / 2) := by
    have hnn : ∀ᵐ z ∂expMeasure 1, 0 ≤ tailWeight a z := ae_of_all _ fun _ ↦ Real.exp_nonneg _
    rw [integral_eq_lintegral_of_nonneg_ae hnn
      (measurable_tailWeight a).aestronglyMeasurable,
      show (∫⁻ z, ENNReal.ofReal (tailWeight a z) ∂expMeasure 1) = _ from lintegral_tailWeight a ha,
      ENNReal.toReal_ofReal (by
        have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)
        linarith [Real.exp_pos (-a / 2)] : 0 ≤ 1 - Real.exp (-a) + 2 * Real.exp (-a / 2))]
    linarith [Real.exp_pos (-a)]
  calc
    μ E = ∫⁻ z, E.indicator (fun _ ↦ (1 : ℝ≥0∞)) z ∂μ := (lintegral_indicator_one hE).symm
    _ ≤ ∫⁻ z, ENNReal.ofReal (G z) ∂μ := lintegral_mono hbound
    _ = ENNReal.ofReal (Real.exp (-d / 2) * (∫ z, tailWeight a z ∂expMeasure 1) ^ Fintype.card ι) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hpos),
        show (∫ z, G z ∂μ) = _ from integral_const_mul _ _,
        integral_fintype_prod_eq_pow (tailWeight a)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (integral_nonneg fun _ ↦ Real.exp_nonneg _) hmoment _) (Real.exp_nonneg _))

end WorkerCompromiseProof.Bounds.Paper
