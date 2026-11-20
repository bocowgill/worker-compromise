/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WorkerCompromiseProof.Core.RowEvents

/-!
# Revealing named rows of a product market

Rows in a fixed partial assignment can be held at arbitrary values. When additional firms are
named, a condition determined by their rows can be imposed before integrating over all other
rows. This is the conditioning step used to sum over candidate extensions selected ex post.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory Set
open scoped ENNReal

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

/-- Keep the named rows of `z` and use `x` for all other rows. -/
def freezeRows (P : Finset ι) (z x : ι → Ω) (i : ι) : Ω := if i ∈ P then z i else x i

omit [Fintype ι] in
theorem measurable_freezeRows (P : Finset ι) :
    Measurable (fun z : (ι → Ω) × (ι → Ω) ↦ freezeRows P z.1 z.2) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i ∈ P
  · simpa [freezeRows, hi, Function.comp_def] using (measurable_pi_apply i).comp
      (measurable_fst : Measurable (@Prod.fst (ι → Ω) (ι → Ω)))
  · simpa [freezeRows, hi, Function.comp_def] using (measurable_pi_apply i).comp
      (measurable_snd : Measurable (@Prod.snd (ι → Ω) (ι → Ω)))

omit [Fintype ι] in
theorem measurable_freezeRows_right (P : Finset ι) (z : ι → Ω) :
    Measurable (freezeRows P z) :=
  (measurable_freezeRows P).comp (measurable_const.prodMk measurable_id)

/-- A rowwise selection from two independent copies has the original product measure. -/
theorem measurePreserving_freezeRows (ν : Measure Ω) [IsProbabilityMeasure ν] (I : Finset ι) :
    let μ := Measure.pi (fun _ : ι ↦ ν)
    MeasurePreserving (fun z : (ι → Ω) × (ι → Ω) ↦ freezeRows I z.1 z.2) (μ.prod μ) μ := by
  let f (i : ι) : Ω × Ω → Ω := if i ∈ I then Prod.fst else Prod.snd
  have h (i : ι) : MeasurePreserving (f i) (ν.prod ν) ν := by
    by_cases hi : i ∈ I
    · simpa [f, hi] using (measurePreserving_fst : MeasurePreserving Prod.fst (ν.prod ν) ν)
    · simpa [f, hi] using (measurePreserving_snd : MeasurePreserving Prod.snd (ν.prod ν) ν)
  have hp := (measurePreserving_pi _ _ h).comp
    (MeasurePreserving.symm _ (measurePreserving_arrowProdEquivProdArrow Ω Ω ι
      (fun _ ↦ ν) (fun _ ↦ ν)))
  convert hp using 1
  funext z i
  by_cases hi : i ∈ I <;> simp [freezeRows, f, hi] <;> rfl

omit [Fintype ι] [MeasurableSpace Ω] in
theorem freezeRows_union (P I : Finset ι) (z x y : ι → Ω) :
    freezeRows (P ∪ I) (freezeRows P z x) y = freezeRows P z (freezeRows I x y) := by
  funext i
  by_cases hp : i ∈ P <;> by_cases hi : i ∈ I <;> simp [freezeRows, hp, hi]

/-- Fubini for re-exposure: resample all rows outside `P ∪ I` after revealing the rows in `I`.
The gate must depend only on the rows in `P ∪ I`. -/
theorem measure_revealRows (ν : Measure Ω) [IsProbabilityMeasure ν]
    (P I : Finset ι) (z : ι → Ω) (A B : Set (ι → Ω))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hlocal : ∀ x y : ι → Ω, (∀ i ∈ P ∪ I, x i = y i) → (x ∈ A ↔ y ∈ A)) :
    let μ := Measure.pi (fun _ : ι ↦ ν)
    μ ((freezeRows P z) ⁻¹' (A ∩ B)) =
      ∫⁻ x, (A.indicator (fun w ↦ μ ((freezeRows (P ∪ I) w) ⁻¹' B))) (freezeRows P z x) ∂μ := by
  classical
  let E := (freezeRows P z) ⁻¹' (A ∩ B)
  have hE : MeasurableSet E := (hA.inter hB).preimage (measurable_freezeRows_right P z)
  let f := fun p : (ι → Ω) × (ι → Ω) ↦ freezeRows I p.1 p.2
  let μ := Measure.pi (fun _ : ι ↦ ν)
  change μ E = _
  rw [← (measurePreserving_freezeRows ν I).measure_preimage hE.nullMeasurableSet,
    Measure.prod_apply (hE.preimage (measurable_freezeRows I))]
  apply lintegral_congr
  intro x
  have heq (y : ι → Ω) :
      freezeRows P z (freezeRows I x y) ∈ A ↔ freezeRows P z x ∈ A := by
    apply hlocal
    intro i hi
    by_cases hp : i ∈ P
    · simp [freezeRows, hp]
    · have hi' := (Finset.mem_union.mp hi).resolve_left hp
      simp [freezeRows, hp, hi']
  by_cases h : freezeRows P z x ∈ A
  · rw [Set.indicator_of_mem h]
    congr 1
    ext y
    change (freezeRows P z (freezeRows I x y) ∈ A ∩ B) ↔ _
    rw [Set.mem_inter_iff, and_iff_right ((heq y).mpr h), ← freezeRows_union]
    rfl
  · rw [Set.indicator_of_notMem h]
    have hnull : Prod.mk x ⁻¹' (f ⁻¹' E) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact h ((heq y).mp hy.1)
    change μ (Prod.mk x ⁻¹' (f ⁻¹' E)) = 0
    rw [hnull, measure_empty]

/-- Conditional child bounds integrated over the newly named rows, with no condition
on whether a skipped row passes a test. -/
theorem measure_revealRows_le (ν : Measure Ω) [IsProbabilityMeasure ν]
    (P I : Finset ι) (z : ι → Ω) (A B : Set (ι → Ω)) (bound : (ι → Ω) → ℝ≥0∞)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hlocal : ∀ x y : ι → Ω, (∀ i ∈ P ∪ I, x i = y i) → (x ∈ A ↔ y ∈ A))
    (hchild : ∀ x, freezeRows P z x ∈ A →
      (Measure.pi (fun _ : ι ↦ ν)) ((freezeRows (P ∪ I) (freezeRows P z x)) ⁻¹' B) ≤
        bound (freezeRows P z x)) :
    let μ := Measure.pi (fun _ : ι ↦ ν)
    μ ((freezeRows P z) ⁻¹' (A ∩ B)) ≤ ∫⁻ x, A.indicator bound (freezeRows P z x) ∂μ := by
  dsimp only
  rw [measure_revealRows ν P I z A B hA hB hlocal]
  apply lintegral_mono
  intro x
  by_cases hx : freezeRows P z x ∈ A
  · simpa only [Set.indicator_of_mem hx] using hchild x hx
  · simp only [Set.indicator_of_notMem hx, le_refl]

end WorkerCompromiseProof.Bounds.Paper
