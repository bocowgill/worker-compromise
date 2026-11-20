/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import WorkerCompromiseProof.Core.SwitchingCostMatching
public import Mathlib.Probability.Moments.Basic

/-!
# Coordinate laws for the paper's edge-score bound

A firm's utility on a fixed edge is independent of the entire ranking column of its
prospective worker. Each utility has the rate-one exponential law.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory ProbabilityTheory SwitchingCostMatching
open scoped ENNReal

private theorem coordIndependent (n w : ℕ) :
    iIndepFun (fun c (p : Profile n w) ↦ p c) (profileMeasureWithWorkers n w) := by
  let := isProbabilityMeasure_expMeasure (r := (1 : ℝ)) zero_lt_one
  exact iIndepFun_pi (μ := fun _ ↦ expMeasure 1) (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)

private theorem coordLaw {n w : ℕ} (c : Bool × Fin n × Fin w) :
    MeasurePreserving (fun p : Profile n w ↦ p c) (profileMeasureWithWorkers n w)
      (expMeasure 1) := by
  let := isProbabilityMeasure_expMeasure (r := (1 : ℝ)) zero_lt_one
  exact measurePreserving_eval (fun _ ↦ expMeasure 1) c

/-- A firm's utility is independent of all the utilities its prospective partner assigns to firms. -/
theorem indepFun_firm_workerColumn {n w : ℕ} (i : Fin n) (j : Fin w) :
    IndepFun (fun p : Profile n w ↦ p (false, i, j))
      (fun (p : Profile n w) (k : Fin n) ↦ p (true, k, j)) (profileMeasureWithWorkers n w) := by
  classical
  let s : Finset (Bool × Fin n × Fin w) := {(false, i, j)}
  let v := (Finset.univ : Finset (Fin n)).image (fun k ↦ (true, k, j))
  have hd : Disjoint s v := by simp [s, v, Finset.disjoint_singleton_left]
  let pick (z : s → ℝ) := z ⟨(false, i, j), by simp [s]⟩
  let column (z : v → ℝ) (k : Fin n) := z ⟨(true, k, j), by simp [v]⟩
  exact ((coordIndependent n w).indepFun_finset s v hd (fun _ ↦ measurable_pi_apply _)).comp
    (show Measurable pick from measurable_pi_apply _)
    (show Measurable column from Measurable.of_eval (fun _ ↦ measurable_pi_apply _))

/-- A fixed worker's vector of firm utilities has product rate-one exponential law. -/
theorem measurePreserving_workerColumn {n w : ℕ} (j : Fin w) :
    MeasurePreserving (fun (p : Profile n w) (k : Fin n) ↦ p (true, k, j))
      (profileMeasureWithWorkers n w) (Measure.pi fun _ : Fin n ↦ expMeasure 1) := by
  let col (k : Fin n) := (true, k, j)
  have hinj : Function.Injective col := fun _ _ h ↦ congrArg (fun c ↦ c.2.1) h
  refine ⟨Measurable.of_eval (fun _ ↦ measurable_pi_apply _), ?_⟩
  change Measure.map (fun (p : Profile n w) (k : Fin n) ↦ p (col k)) _ = _
  rw [((coordIndependent n w).precomp hinj).map_fun_eq_pi_map
    (fun k ↦ (measurable_pi_apply (col k)).aemeasurable)]
  simp_rw [(coordLaw (col _)).map_eq]

private theorem lintegral_exp_utility {t : ℝ} (ht : t < 1) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (t * x)) ∂expMeasure 1) =
      ENNReal.ofReal (1 - t)⁻¹ := by
  change (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (t * x))
      ∂(volume.withDensity (exponentialPDF 1))) = _
  have hexp (r : ℝ) : Measurable (exponentialPDF r) :=
    (measurable_exponentialPDFReal r).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul volume (hexp 1) (by fun_prop)]
  have h : exponentialPDF 1 * (fun x : ℝ ↦ ENNReal.ofReal (Real.exp (t * x))) =
      fun x ↦ ENNReal.ofReal ((1 - t)⁻¹) * exponentialPDF (1 - t) x := by
    funext x
    by_cases hx : 0 ≤ x
    · simp only [Pi.mul_apply, exponentialPDF_of_nonneg hx, one_mul,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr (sub_nonneg.mpr ht.le)), ← Real.exp_add]
      congr 1
      rw [← mul_assoc, inv_mul_cancel₀ (sub_pos.mpr ht).ne', one_mul]
      congr 1
      ring
    · rw [Pi.mul_apply, exponentialPDF_of_neg (lt_of_not_ge hx),
        exponentialPDF_of_neg (lt_of_not_ge hx), zero_mul, mul_zero]
  rw [h, lintegral_const_mul _ (hexp _), lintegral_exponentialPDF_eq_one (sub_pos.mpr ht),
    mul_one]

theorem integrable_exp_edgeUtility {n w : ℕ} (c : Bool × Fin n × Fin w) {t : ℝ} (ht : t < 1) :
    Integrable (fun p : Profile n w ↦ Real.exp (t * p c)) (profileMeasureWithWorkers n w) := by
  apply (coordLaw c).integrable_comp_of_integrable (g := fun x ↦ Real.exp (t * x))
  refine ⟨(by fun_prop), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ (Real.exp_pos (t * x)).le),
    lintegral_exp_utility ht]
  exact ENNReal.ofReal_lt_top

/-- The single-coordinate moment generating function in the original market. -/
theorem integral_exp_edgeUtility {n w : ℕ} (c : Bool × Fin n × Fin w) {t : ℝ} (ht : t < 1) :
    (∫ p : Profile n w, Real.exp (t * p c) ∂profileMeasureWithWorkers n w) = (1 - t)⁻¹ := by
  calc
    _ = ∫ x : ℝ, Real.exp (t * x) ∂expMeasure 1 := by
      rw [← (coordLaw c).map_eq, integral_map (coordLaw c).measurable.aemeasurable (by fun_prop)]
    _ = _ := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ (Real.exp_pos (t * x)).le)
          (by fun_prop), lintegral_exp_utility ht,
        ENNReal.toReal_ofReal (inv_nonneg.mpr (sub_nonneg.mpr ht.le))]

end WorkerCompromiseProof.Bounds.Paper
