/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WorkerCompromiseProof.Rescale
public import WorkerCompromiseProof.Tilt

/-!
# Slicing the firm sum after rescaling worker marks

For a fixed injection with firm sum $S$, rescaling the worker marks leaves
a factor $(q ^ 2S)^{-n}$ and a tail probability for independent exponential
variables. On $S \ge s$ the tail probability is largest at $s$. The remaining
firm integral is the logarithmic simplex slice from the paper.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory Set
open scoped BigOperators ENNReal

private theorem cube_support {ι : Type*} [Fintype ι] :
    ∀ᵐ y ∂Measure.pi (fun _ : ι ↦ volume.restrict (Icc (0 : ℝ) 1)),
      ∀ i, y i ∈ Icc (0 : ℝ) 1 := by
  rw [← Measure.restrict_pi_pi]
  simpa only [mem_univ_pi] using ae_restrict_mem
    (μ := Measure.pi (fun _ : ι ↦ (volume : Measure ℝ)))
    (MeasurableSet.univ_pi fun _ : ι ↦ measurableSet_Icc)

private theorem cube_le_orthant {ι : Type*} [Fintype ι] :
    Measure.pi (fun _ : ι ↦ volume.restrict (Icc (0 : ℝ) 1)) ≤
      Measure.pi (fun _ : ι ↦ volume.restrict (Ici (0 : ℝ))) := by
  simp_rw [← Measure.restrict_pi_pi]
  apply Measure.restrict_mono _ le_rfl
  intro _ h i hi
  exact (h i hi).1

/-- On the worker cube the vacancy pays for the missing diagonal terms. On the
orthant the resulting exponential integral is a scaled probability. -/
theorem workerCube_le_rescaled_tail {ι : Type*} [Fintype ι] [DecidableEq ι] {q b B : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (x : ι → ℝ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1)
    (hr : 0 < q ^ 2 * ∑ i, x i) :
    let r := q ^ 2 * ∑ i, x i
    (∫⁻ y in {y : ι → ℝ | B ≤ workerTailMass b y},
        ENNReal.ofReal (vacancyStabilityProduct q x y)
          ∂(Measure.pi (fun _ : ι ↦ volume.restrict (Icc (0 : ℝ) 1)))) ≤
      ENNReal.ofReal r⁻¹ ^ Fintype.card ι * expTail ι r b B := by
  let E := {y : ι → ℝ | B ≤ workerTailMass b y}
  let r := q ^ 2 * ∑ i, x i
  let f (y : ι → ℝ) := ENNReal.ofReal (Real.exp (-(r * ∑ j, y j)))
  calc
    _ ≤ ∫⁻ y in E, f y ∂Measure.pi (fun _ : ι ↦ volume.restrict (Icc (0 : ℝ) 1)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae (cube_support (ι := ι))] with y hy
      exact ENNReal.ofReal_le_ofReal (vacancyStabilityProduct_le_exp x y hq hx hy)
    _ ≤ ∫⁻ y in E, f y ∂Measure.pi (fun _ : ι ↦ volume.restrict (Ici (0 : ℝ))) :=
      lintegral_mono' (Measure.restrict_mono Subset.rfl cube_le_orthant) le_rfl
    _ = _ := workerTail_lintegral_rescale hr b B

/-- The fixed-injection double integral, before the exponential Markov bound.
Here $n + 1$ is the number of firms and $n!$ occurs in the simplex slice. -/
theorem fixedInjection_lintegral_le_expTail (n : ℕ) {q s b B : ℝ}
    (hq : q ∈ Ioc (0 : ℝ) 1) (hs : 0 < s) (hsn : s ≤ (n : ℝ) + 1)
    (hb : 0 ≤ b) (hB : 0 ≤ B) :
    let μ := Measure.pi (fun _ : Fin (n + 1) ↦ volume.restrict (Icc (0 : ℝ) 1))
    (∫⁻ x : Fin (n + 1) → ℝ in {x | s ≤ ∑ i, x i},
        ∫⁻ y in {y : Fin (n + 1) → ℝ | B ≤ workerTailMass b y},
          ENNReal.ofReal (vacancyStabilityProduct q x y) ∂μ ∂μ) ≤
      expTail (Fin (n + 1)) (q ^ 2 * s) b B *
        ENNReal.ofReal ((q ^ 2)⁻¹ ^ (n + 1) * (Real.log (((n : ℝ) + 1) / s) / n.factorial)) := by
  let μ := Measure.pi (fun _ : Fin (n + 1) ↦ volume.restrict (Icc (0 : ℝ) 1))
  let E := {x : Fin (n + 1) → ℝ | s ≤ ∑ i, x i}
  let p := expTail (Fin (n + 1)) (q ^ 2 * s) b B
  let c := p * ENNReal.ofReal ((q ^ 2)⁻¹ ^ (n + 1))
  have hE : MeasurableSet E := measurableSet_le measurable_const (by fun_prop)
  change (∫⁻ x in E, ∫⁻ y in {y | B ≤ workerTailMass b y},
    ENNReal.ofReal (vacancyStabilityProduct q x y) ∂μ ∂μ) ≤ _
  calc
    _ ≤ ∫⁻ x in E, c * ENNReal.ofReal (((∑ j, x j) : ℝ)⁻¹ ^ (n + 1)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hE, ae_restrict_of_ae (cube_support (ι := Fin (n + 1)))]
        with x hxE hx
      let S := ∑ j, x j
      have hS : s ≤ S := hxE
      have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq.1
      have hr : 0 < q ^ 2 * S := mul_pos hq2 (hs.trans_le hS)
      refine (workerCube_le_rescaled_tail ⟨hq.1.le, hq.2⟩ x hx hr).trans ?_
      have htail : expTail (Fin (n + 1)) (q ^ 2 * S) b B ≤ p :=
        expTail_antitone (mul_le_mul_of_nonneg_left hS hq2.le) (mul_nonneg hq2.le hs.le) hb hB
      change ENNReal.ofReal ((q ^ 2 * S)⁻¹) ^ Fintype.card (Fin (n + 1)) *
        expTail (Fin (n + 1)) (q ^ 2 * S) b B ≤ c * ENNReal.ofReal (S⁻¹ ^ (n + 1))
      calc
        _ ≤ ENNReal.ofReal ((q ^ 2 * S)⁻¹) ^ Fintype.card (Fin (n + 1)) * p :=
          mul_le_mul_right htail _
        _ = _ := by
          simp only [c, Fintype.card_fin, mul_inv, ENNReal.ofReal_mul (inv_nonneg.mpr hq2.le),
            mul_pow, ENNReal.ofReal_pow (inv_nonneg.mpr (hs.trans_le hS).le),
            ENNReal.ofReal_pow (inv_nonneg.mpr hq2.le)]
          ac_rfl
    _ = c * (∫⁻ x in E, ENNReal.ofReal (((∑ j, x j) : ℝ)⁻¹ ^ (n + 1)) ∂μ) :=
      lintegral_const_mul _ (by fun_prop)
    _ ≤ c * ENNReal.ofReal (Real.log (((n : ℝ) + 1) / s) / n.factorial) :=
      mul_le_mul_right (markCube_lintegral_inv_sum_pow_le n hs hsn) _
    _ = _ := by
      simp only [c, p, ENNReal.ofReal_mul (show 0 ≤ (q ^ 2)⁻¹ ^ (n + 1) by positivity)]
      ac_rfl

/-- The paper's bound on the fixed-injection double integral follows by applying
the exponential tail bound once, at the smallest allowed firm sum. -/
theorem vacancyStabilityProduct_tail_double_lintegral_le (n : ℕ) {q s b B : ℝ}
    (hq : q ∈ Ioc (0 : ℝ) 1) (hs : 0 < s) (hsn : s ≤ (n : ℝ) + 1)
    (hb : 0 ≤ b) (hB : 0 ≤ B) :
    let μ := Measure.pi (fun _ : Fin (n + 1) ↦ volume.restrict (Icc (0 : ℝ) 1))
    (∫⁻ x : Fin (n + 1) → ℝ in {x | s ≤ ∑ i, x i},
        ∫⁻ y in {y : Fin (n + 1) → ℝ | B ≤ workerTailMass b y},
          ENNReal.ofReal (vacancyStabilityProduct q x y) ∂μ ∂μ) ≤
      ENNReal.ofReal
        ((q ^ 2)⁻¹ ^ (n + 1) * Real.exp (-(q ^ 2 * s * B) / 2) *
          (1 + 2 * Real.exp (-(q ^ 2 * s * b) / 2)) ^ (n + 1) *
          (Real.log (((n : ℝ) + 1) / s) / (n.factorial : ℝ))) := by
  apply (fixedInjection_lintegral_le_expTail n hq hs hsn hb hB).trans
  have ht := measure_exponentialWorkerTail_le (ι := Fin (n + 1))
    (a := q ^ 2 * s * b) (d := q ^ 2 * s * B) (mul_nonneg (mul_nonneg (sq_nonneg q) hs.le) hb)
  change expTail (Fin (n + 1)) (q ^ 2 * s) b B ≤ _ at ht
  calc
    _ ≤ _ := mul_le_mul_left ht _
    _ = _ := by
      rw [Fintype.card_fin, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end WorkerCompromiseProof.Bounds.Paper
