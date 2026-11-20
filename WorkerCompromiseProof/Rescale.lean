/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WorkerCompromiseProof.Core.TailIntegral
public import WorkerCompromiseProof.ExpDensity
public import WorkerCompromiseProof.Orthant

/-!
# Rescaling the worker integral

At fixed positive rate `r`, the substitution `z = r y` expresses the worker
integral as the volume factor `r⁻ⁿ` times the probability of a tail event for
independent rate-one exponential random variables. Increasing the rate raises
both the minimum qualifying coordinate and the required total.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Probability that the qualifying rate-one exponential coordinates meet the
rescaled total. -/
noncomputable def expTail (ι : Type*) [Fintype ι] (r b B : ℝ) : ℝ≥0∞ :=
  (Measure.pi (fun _ : ι ↦ expMeasure 1)) {z | r * B ≤ workerTailMass (r * b) z}

private theorem workerTailMass_scale {ι : Type*} [Fintype ι]
    {r : ℝ} (hr : 0 < r) (b : ℝ) (y : ι → ℝ) :
    workerTailMass (r * b) (fun i ↦ r * y i) = r * workerTailMass b y := by
  simp only [workerTailMass, Finset.mul_sum, mul_le_mul_iff_right₀ hr, mul_ite, mul_zero]

/-- Substitution in the nonnegative orthant. Both thresholds scale along with
the realization, and the volume contributes one inverse rate per worker. -/
theorem workerTail_lintegral_rescale {ι : Type*} [Fintype ι] {r : ℝ}
    (hr : 0 < r) (b B : ℝ) :
    (∫⁻ y in {y : ι → ℝ | B ≤ workerTailMass b y}, ENNReal.ofReal (Real.exp (-(r * ∑ j, y j)))
      ∂(Measure.pi (fun _ : ι ↦ volume.restrict (Ici (0 : ℝ))))) =
    ENNReal.ofReal r⁻¹ ^ Fintype.card ι * expTail ι r b B := by
  let μ := Measure.pi (fun _ : ι ↦ volume.restrict (Ici (0 : ℝ)))
  let g (y : ι → ℝ) (i : ι) := r * y i
  let f (z : ι → ℝ) := ENNReal.ofReal (Real.exp (-(∑ i, z i)))
  let E := {z : ι → ℝ | r * B ≤ workerTailMass (r * b) z}
  have hg : Measurable g := by fun_prop
  have hf : Measurable f := by fun_prop
  have hE : MeasurableSet E :=
    measurableSet_le measurable_const (measurable_workerTailMass _)
  have hpre : g ⁻¹' E = {y : ι → ℝ | B ≤ workerTailMass b y} := by
    ext y
    change (r * B ≤ workerTailMass (r * b) (fun i ↦ r * y i)) ↔ _
    rw [workerTailMass_scale hr, mul_le_mul_iff_right₀ hr]
    rfl
  have hmap : μ.map g = (ENNReal.ofReal r⁻¹ ^ Fintype.card ι) • μ := map_orthant_mul hr
  have hdens : μ.withDensity f = Measure.pi (fun _ : ι ↦ expMeasure 1) :=
    orthant_withDensity_exp_neg_sum ι
  calc
    _ = ∫⁻ y in g ⁻¹' E, f (g y) ∂μ := by
      simp only [hpre, μ, f, g, ← Finset.mul_sum]
    _ = ∫⁻ z in E, f z ∂μ.map g := (setLIntegral_map hE hf hg).symm
    _ = _ := by
      rw [hmap, setLIntegral_smul_measure, ← withDensity_apply f hE, hdens]
      rfl

/-- For nonnegative thresholds, a larger rate makes both requirements harder. -/
theorem expTail_antitone {ι : Type*} [Fintype ι] {r s b B : ℝ}
    (hrs : s ≤ r) (hs : 0 ≤ s) (hb : 0 ≤ b) (hB : 0 ≤ B) :
    expTail ι r b B ≤ expTail ι s b B := by
  apply measure_mono
  intro z hz
  refine (mul_le_mul_of_nonneg_right hrs hB).trans (hz.trans ?_)
  unfold workerTailMass
  apply Finset.sum_le_sum
  intro i _
  have hcut := mul_le_mul_of_nonneg_right hrs hb
  by_cases hi : r * b ≤ z i
  · simp [hi, hcut.trans hi]
  · simp only [ite_eq_right hi]
    split_ifs with hz'
    · exact (mul_nonneg hs hb).trans hz'
    · exact le_rfl

end WorkerCompromiseProof.Bounds.Paper
