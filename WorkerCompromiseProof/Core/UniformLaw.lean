/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib
public import WorkerCompromiseProof.Core.SwitchingCostMatching
public import WorkerCompromiseProof.Core.Realization
public import WorkerCompromiseProof.Core.RowEvents

/-!
# The uniform marks of an exponential market

Taking the exponential of the negative utility turns independent rate-one exponential
utilities into independent uniform marks. The map is extended to negative utilities by
capping the mark at one so it takes values in the unit interval on every profile.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The exponential tail mark, extended to negative inputs. -/
noncomputable def uniformMark (x : ℝ) : unitInterval :=
  ⟨min (Real.exp (-x)) 1, le_min (Real.exp_pos (-x)).le zero_le_one, min_le_right _ _⟩

theorem measurable_uniformMark : Measurable uniformMark :=
  ((Real.continuous_exp.comp continuous_neg).min continuous_const).measurable.subtype_mk

theorem coe_uniformMark_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    (uniformMark x : ℝ) = Real.exp (-x) := by
  change min (Real.exp (-x)) 1 = _
  exact min_eq_left (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx))

private theorem expMeasureReal_Ici {a : ℝ} (ha : 0 ≤ a) :
    (expMeasure 1).real (Ici a) = Real.exp (-a) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  let : NullSingletonClass (expMeasure 1) := by
    unfold expMeasure gammaMeasure
    infer_instance
  have he : (expMeasure 1) (Ici a) = (expMeasure 1) (Ioi a) :=
    measure_congr Ioi_ae_eq_Ici.symm
  rw [measureReal_def, he, ← measureReal_def, ← compl_Iic,
    probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real,
    cdf_expMeasure_eq zero_lt_one, ite_eq_left ha, one_mul]
  ring

/-- A rate-one exponential utility yields a uniform tail mark. -/
theorem measurePreserving_uniformMark : MeasurePreserving uniformMark (expMeasure 1) volume := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  refine ⟨measurable_uniformMark, ?_⟩
  apply Measure.ext_of_Iic
  intro a
  rw [Measure.map_apply measurable_uniformMark measurableSet_Iic, unitInterval.volume_Iic]
  by_cases ha : (a : ℝ) = 1
  · have hp : uniformMark ⁻¹' Iic a = univ := by
      ext x
      change (uniformMark x : ℝ) ≤ (a : ℝ) ↔ x ∈ univ
      simp [ha, (uniformMark x).2.2]
    simp [hp, ha]
  have ha' : (a : ℝ) < 1 := lt_of_le_of_ne a.2.2 ha
  by_cases hzero : (a : ℝ) = 0
  · have hp : uniformMark ⁻¹' Iic a = ∅ := by
      ext x
      change min (Real.exp (-x)) 1 ≤ (a : ℝ) ↔ x ∈ ∅
      simp [hzero, not_le_of_gt (Real.exp_pos _)]
    simp [hp, hzero]
  have hpos : 0 < (a : ℝ) := lt_of_le_of_ne a.2.1 (Ne.symm hzero)
  have hp : uniformMark ⁻¹' Iic a = Ici (-Real.log (a : ℝ)) := by
    ext x
    change min (Real.exp (-x)) 1 ≤ (a : ℝ) ↔ -Real.log (a : ℝ) ≤ x
    rw [min_le_iff, or_iff_left (not_le.mpr ha'), ← Real.le_log_iff_exp_le hpos]
    constructor <;> intro h <;> linarith
  rw [hp, ← ENNReal.ofReal_toReal (measure_ne_top _ _), ← measureReal_def,
    expMeasureReal_Ici (neg_nonneg.mpr (Real.log_nonpos hpos.le a.2.2)), neg_neg,
    Real.exp_log hpos]

/-- Exponential utility is positive almost surely. -/
theorem ae_expMeasure_pos : ∀ᵐ x ∂expMeasure 1, 0 < x := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  have hcdf := cdf_expMeasure_eq (r := 1) zero_lt_one 0
  rw [cdf_eq_real] at hcdf
  have hz : (expMeasure 1).real (Iic (0 : ℝ)) = 0 := by simpa using hcdf
  rw [ae_iff]
  simp only [not_lt]
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hz

/-- Every coordinate of the original profile lies in the exponential support almost surely. -/
theorem ae_profile_utilities_pos (n w : ℕ) :
    ∀ᵐ p ∂SwitchingCostMatching.profileMeasureWithWorkers n w, ∀ ij, 0 < p ij := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  apply ae_all_iff.mpr
  intro ij
  have h := measurePreserving_eval (fun _ : Bool × Fin n × Fin w ↦ expMeasure 1) ij
  exact h.quasiMeasurePreserving.ae ae_expMeasure_pos

/-- Currying a product of two finite coordinate types preserves the product law. -/
theorem measurePreserving_curryFinite {ι κ A : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ A)
      (Measure.pi fun _ : ι × κ ↦ μ)
      (Measure.pi fun _ : ι ↦ Measure.pi fun _ : κ ↦ μ) := by
  apply MeasurePreserving.symm (MeasurableEquiv.curry ι κ A).symm
  refine ⟨(MeasurableEquiv.curry ι κ A).symm.measurable, (Measure.pi_eq fun s _ ↦ ?_).symm⟩
  rw [MeasurableEquiv.map_apply]
  have he :
      (MeasurableEquiv.curry ι κ A).symm ⁻¹' (univ.pi s) =
        univ.pi fun i ↦ univ.pi fun j ↦ s (i, j) := by
    ext x
    simp [MeasurableEquiv.coe_curry_symm, Function.uncurry, Prod.forall]
  simp only [he, Measure.pi_pi, Fintype.prod_prod_type]

private theorem measurePreserving_boolPair {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (fun x : Bool → A ↦ (x false, x true)) (Measure.pi fun _ : Bool ↦ μ)
      (μ.prod μ) := by
  have hl := measurePreserving_piCongrLeft (fun _ : Fin 2 ↦ μ) finTwoEquiv.symm
  exact (measurePreserving_finTwoArrow μ).comp hl

private def profileCoordinates (n w : ℕ) : Bool × Fin n × Fin w ≃ Fin n × Fin w × Bool where
  toFun i := (i.2.1, i.2.2, i.1)
  invFun i := (i.2.2, i.1, i.2.1)
  left_inv := by rintro ⟨b, i, j⟩; rfl
  right_inv := by rintro ⟨i, j, b⟩; rfl

/-- Arrange the exponential tail marks by firm, worker and side. -/
noncomputable def profileUniformMarks {n w : ℕ} (p : SwitchingCostMatching.Profile n w) :
    MarksProfile n w :=
  fun i j ↦ (uniformMark (p (false, i, j)), uniformMark (p (true, i, j)))

/-- The law on the array of tail marks is the product of the uniform laws. -/
theorem measurePreserving_profileUniformMarks (n w : ℕ) :
    MeasurePreserving (@profileUniformMarks n w)
      (SwitchingCostMatching.profileMeasureWithWorkers n w) (marksProfileMeasure n w) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  let ν : Measure unitInterval := volume
  have hmark := measurePreserving_pi (fun _ : Bool × Fin n × Fin w ↦ expMeasure 1)
    (fun _ ↦ ν) (fun _ ↦ measurePreserving_uniformMark)
  have hcoords := measurePreserving_piCongrLeft (fun _ : Fin n × Fin w × Bool ↦ ν)
    (profileCoordinates n w)
  have hrows := measurePreserving_curryFinite (ι := Fin n) (κ := Fin w × Bool) ν
  have hcols := measurePreserving_pi
    (fun _ : Fin n ↦ Measure.pi fun _ : Fin w × Bool ↦ ν)
    (fun _ ↦ Measure.pi fun _ : Fin w ↦ Measure.pi fun _ : Bool ↦ ν)
    (fun _ ↦ measurePreserving_curryFinite (ι := Fin w) (κ := Bool) ν)
  have hpair := measurePreserving_pi
    (fun _ : Fin n ↦ Measure.pi fun _ : Fin w ↦ Measure.pi fun _ : Bool ↦ ν)
    (fun _ ↦ Measure.pi fun _ : Fin w ↦ ν.prod ν)
    (fun _ ↦ measurePreserving_pi (fun _ : Fin w ↦ Measure.pi fun _ : Bool ↦ ν)
      (fun _ ↦ ν.prod ν) (fun _ ↦ measurePreserving_boolPair ν))
  exact hpair.comp (hcols.comp (hrows.comp (hcoords.comp hmark)))

/-- The profile marks equal the untruncated exponential marks almost surely. -/
theorem ae_profileUniformMarks_eq_exp_neg (n w : ℕ) :
    ∀ᵐ p ∂SwitchingCostMatching.profileMeasureWithWorkers n w,
      ∀ i : Fin n, ∀ j : Fin w,
        ((profileUniformMarks p i j).1 : ℝ) = Real.exp (-p (false, i, j)) ∧
          ((profileUniformMarks p i j).2 : ℝ) = Real.exp (-p (true, i, j)) :=
  (ae_profile_utilities_pos n w).mono fun p hp i j ↦ by
    exact ⟨coe_uniformMark_of_nonneg (hp (false, i, j)).le,
      coe_uniformMark_of_nonneg (hp (true, i, j)).le⟩

/-- In particular both vectors of assigned marks coincide with their raw utility formulas. -/
theorem ae_profileUniformMarks_matching_eq_exp_neg (n w : ℕ) :
    ∀ᵐ p ∂SwitchingCostMatching.profileMeasureWithWorkers n w,
      ∀ m : SwitchingCostMatching.Matching n w,
        (fun i ↦ ((profileUniformMarks p i (m i)).1 : ℝ)) =
            (fun i ↦ Real.exp (-p (false, i, m i))) ∧
          (fun i ↦ ((profileUniformMarks p i (m i)).2 : ℝ)) =
            (fun i ↦ Real.exp (-p (true, i, m i))) :=
  (ae_profileUniformMarks_eq_exp_neg n w).mono fun _ hp m ↦
    ⟨funext fun i ↦ (hp i (m i)).1, funext fun i ↦ (hp i (m i)).2⟩

/-- The uniform-mark model preserves stability on nonnegative profiles. -/
theorem marksStable_profileUniformMarks_iff {n w : ℕ} {p : SwitchingCostMatching.Profile n w}
    (hp : ∀ ij, 0 ≤ p ij) (ε : ℝ) (m : SwitchingCostMatching.Matching n w) :
    MarksStable (fun i j ↦ ((profileUniformMarks p i j).1 : ℝ))
      (fun i j ↦ ((profileUniformMarks p i j).2 : ℝ)) (Real.exp (-ε)) m ↔
        SwitchingCostMatching.IsStable p ε m := by
  simpa only [profileUniformMarks, coe_uniformMark_of_nonneg (hp _)] using
    marksStable_exp_neg_iff p ε m

/-- The original and uniform-mark stability events agree almost surely for all matchings. -/
theorem ae_marksStable_profileUniformMarks_iff (n w : ℕ) (ε : ℝ) :
    ∀ᵐ p ∂SwitchingCostMatching.profileMeasureWithWorkers n w,
      ∀ m : SwitchingCostMatching.Matching n w,
        MarksStable (fun i j ↦ ((profileUniformMarks p i j).1 : ℝ))
          (fun i j ↦ ((profileUniformMarks p i j).2 : ℝ)) (Real.exp (-ε)) m ↔
            SwitchingCostMatching.IsStable p ε m :=
  (ae_profile_utilities_pos n w).mono fun _ hp m ↦
    marksStable_profileUniformMarks_iff (fun ij ↦ (hp ij).le) ε m

end WorkerCompromiseProof.Bounds
