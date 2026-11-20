/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Scaling Lebesgue measure on the nonnegative orthant

The diagonal change of variables used after fixing the sum of the firm marks
preserves the orthant and contributes one inverse rate per worker.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory Set
open scoped ENNReal

/-- Scaling every worker mark by the same positive rate in the nonnegative orthant. -/
theorem map_orthant_mul {ι : Type*} [Fintype ι] {r : ℝ} (hr : 0 < r) :
    (Measure.pi (fun _ : ι ↦ volume.restrict (Ici (0 : ℝ)))).map (fun y i ↦ r * y i) =
      ENNReal.ofReal r⁻¹ ^ Fintype.card ι •
        Measure.pi (fun _ : ι ↦ volume.restrict (Ici (0 : ℝ))) := by
  let C : Set (ι → ℝ) := univ.pi (fun _ ↦ Ici 0)
  have hC : MeasurableSet C := MeasurableSet.univ_pi fun _ ↦ measurableSet_Ici
  have hpre : (fun y : ι → ℝ ↦ r • y) ⁻¹' C = C := by
    ext x
    change (∀ i ∈ (univ : Set ι), 0 ≤ r * x i) ↔ ∀ i ∈ (univ : Set ι), 0 ≤ x i
    simp [hr]
  have hvol : Measure.pi (fun _ : ι ↦ volume.restrict (Ici (0 : ℝ))) =
      (volume : Measure (ι → ℝ)).restrict C := by
    rw [volume_pi, Measure.restrict_pi_pi]
  rw [hvol]
  change ((volume : Measure (ι → ℝ)).restrict C).map (r • ·) = _
  have he := Measure.restrict_map (μ := (volume : Measure (ι → ℝ)))
    (measurable_const_smul r) hC
  rw [hpre] at he
  rw [← he, Measure.map_addHaar_smul volume hr.ne', Measure.restrict_smul, Module.finrank_pi,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _)), ← inv_pow,
    ENNReal.ofReal_pow (inv_nonneg.mpr hr.le)]

end WorkerCompromiseProof.Bounds.Paper
