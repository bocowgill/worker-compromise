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
# Fixed-injection stability and the assigned marks

Separating the graph of a fixed injection from the remaining coordinates gives the exact
product formula for the stability probability with a restriction on the assigned marks.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds

open MeasureTheory Set SwitchingCostMatching
open scoped BigOperators ENNReal

/-- All assigned edge marks, indexed by the firm of the fixed injection. -/
def assignedCells {n w : ℕ} (m : Matching n w) (p : MarksProfile n w) : Fin n → MarksCell :=
  fun i ↦ p i (m i)

/-- Coordinates of edges outside the assigned graph. -/
abbrev OffAssignment {n w : ℕ} (m : Matching n w) :=
  {i : Fin n × Fin w // i.2 ≠ m i.1}

/-- Separate the assigned edge marks from all other edge marks. -/
def splitAssignedCells {n w : ℕ} (m : Matching n w) (p : MarksProfile n w) :
    (Fin n → MarksCell) × (OffAssignment m → MarksCell) :=
  (assignedCells m p, fun e ↦ p e.val.1 e.val.2)

private theorem measurePreserving_flattenMarks (n w : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin n) (Fin w) MarksCell).symm
      (marksProfileMeasure n w) (Measure.pi fun _ : Fin n × Fin w ↦ marksCellMeasure) := by
  refine ⟨(MeasurableEquiv.curry (Fin n) (Fin w) MarksCell).symm.measurable,
    (Measure.pi_eq fun s _ ↦ ?_).symm⟩
  rw [MeasurableEquiv.map_apply]
  have he : (MeasurableEquiv.curry (Fin n) (Fin w) MarksCell).symm ⁻¹' (univ.pi s) =
      univ.pi (fun i ↦ univ.pi (fun j ↦ s (i, j))) := by
    ext x
    simp [MeasurableEquiv.coe_curry_symm, Function.uncurry, Prod.forall]
  simp only [he, marksProfileMeasure, marksRowMeasure, Measure.pi_pi, Fintype.prod_prod_type]

private def assignmentGraphEquiv {n w : ℕ} (m : Matching n w) :
    Fin n ≃ {e : Fin n × Fin w // e.2 = m e.1} where
  toFun i := ⟨(i, m i), rfl⟩
  invFun e := e.val.1
  left_inv _ := rfl
  right_inv e := by
    apply Subtype.ext
    exact Prod.ext rfl e.property.symm

private theorem measurePreserving_splitAssignedCells {n w : ℕ} (m : Matching n w) :
    MeasurePreserving (splitAssignedCells m) (marksProfileMeasure n w)
      ((Measure.pi fun _ : Fin n ↦ marksCellMeasure).prod
        (Measure.pi fun _ : OffAssignment m ↦ marksCellMeasure)) := by
  let A := {e : Fin n × Fin w // e.2 = m e.1}
  let B := OffAssignment m
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ MarksCell) (assignmentGraphEquiv m).symm
  have hgraph : MeasurePreserving E (Measure.pi fun _ : A ↦ marksCellMeasure)
      (Measure.pi fun _ : Fin n ↦ marksCellMeasure) :=
    measurePreserving_piCongrLeft (fun _ : Fin n ↦ marksCellMeasure) (assignmentGraphEquiv m).symm
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (α := fun _ : Fin n × Fin w ↦ MarksCell) (fun _ ↦ marksCellMeasure) (fun e ↦ e.2 = m e.1)
  have hindex : MeasurePreserving (Prod.map E (id : (B → MarksCell) → B → MarksCell))
      ((Measure.pi fun _ : A ↦ marksCellMeasure).prod (Measure.pi fun _ : B ↦ marksCellMeasure))
      ((Measure.pi fun _ : Fin n ↦ marksCellMeasure).prod (Measure.pi fun _ : B ↦ marksCellMeasure)) := by
    refine ⟨hgraph.measurable.prodMap measurable_id, ?_⟩
    rw [← Measure.map_prod_map _ _ hgraph.measurable measurable_id, hgraph.map_eq, Measure.map_id]
  exact hindex.comp (hsplit.comp (measurePreserving_flattenMarks n w))

def noBlockCell {n w : ℕ} (m : Matching n w) (q : ℝ) (d : Fin n → MarksCell)
    (e : OffAssignment m) : Set MarksCell :=
  {z | ¬ ((z.1 : ℝ) < q * (d e.val.1).1 ∧
     ∀ k, m k = e.val.2 → (z.2 : ℝ) < q * (d k).2)}

/-- Stability and any measurable assigned-mark condition can be integrated over the assigned
coordinates, multiplying the independent probabilities of no block on the other coordinates. -/
theorem marksProfileMeasure_stable_assignedCells_eq_lintegral {n w : ℕ} (m : Matching n w) (q : ℝ)
    (s : Set (Fin n → MarksCell)) (hs : MeasurableSet s) :
    marksProfileMeasure n w
      {p | MarksStable (fun i j ↦ (p i j).1.val) (fun i j ↦ (p i j).2.val) q m ∧
        assignedCells m p ∈ s} =
      ∫⁻ d in s, (∏ e : OffAssignment m, marksCellMeasure (noBlockCell m q d e))
        ∂Measure.pi (fun _ : Fin n ↦ marksCellMeasure) := by
  let S : Set ((Fin n → MarksCell) × (OffAssignment m → MarksCell)) :=
    {z | z.1 ∈ s ∧ ∀ e, z.2 e ∈ noBlockCell m q z.1 e}
  have hS : MeasurableSet S := by
    change MeasurableSet
      {z : (Fin n → MarksCell) × (OffAssignment m → MarksCell) |
        z.1 ∈ s ∧ ∀ e : OffAssignment m, ¬ (((z.2 e).1 : ℝ) < q * (z.1 e.val.1).1 ∧
          ∀ k, m k = e.val.2 → ((z.2 e).2 : ℝ) < q * (z.1 k).2)}
    have hb (e : OffAssignment m) : MeasurableSet
        {z : (Fin n → MarksCell) × (OffAssignment m → MarksCell) |
          ¬ (((z.2 e).1 : ℝ) < q * (z.1 e.val.1).1 ∧
            ∀ k, m k = e.val.2 → ((z.2 e).2 : ℝ) < q * (z.1 k).2)} := by
      apply MeasurableSet.compl
      change MeasurableSet {z : (Fin n → MarksCell) × (OffAssignment m → MarksCell) |
        ((z.2 e).1 : ℝ) < q * (z.1 e.val.1).1 ∧
          ∀ k, m k = e.val.2 → ((z.2 e).2 : ℝ) < q * (z.1 k).2}
      rw [Set.ofPred_and]
      apply MeasurableSet.inter
      · exact measurableSet_lt (by fun_prop) (by fun_prop)
      · rw [Set.ofPred_forall]
        apply MeasurableSet.iInter
        intro k
        by_cases hk : m k = e.val.2
        · simpa only [hk, true_implies] using
            (measurableSet_lt (by fun_prop) (by fun_prop) :
              MeasurableSet {z : (Fin n → MarksCell) × (OffAssignment m → MarksCell) |
                ((z.2 e).2 : ℝ) < q * (z.1 k).2})
        · simp [hk]
    rw [Set.ofPred_and, Set.ofPred_forall]
    exact (measurable_fst hs).inter (MeasurableSet.iInter hb)
  have hpre : splitAssignedCells m ⁻¹' S =
      {p | MarksStable (fun i j ↦ (p i j).1.val) (fun i j ↦ (p i j).2.val) q m ∧
        assignedCells m p ∈ s} := by
    ext p
    simp only [S, splitAssignedCells, mem_preimage, mem_ofPred_eq, noBlockCell]
    constructor
    · rintro ⟨hd, h⟩
      refine ⟨fun i j hj hX hY ↦ h ⟨(i, j), hj⟩ ⟨hX, ?_⟩, hd⟩
      intro k hk
      simpa only [assignedCells, hk] using hY k hk
    · rintro ⟨h, hd⟩
      refine ⟨hd, fun e hxy ↦ h e.val.1 e.val.2 e.property hxy.1 ?_⟩
      intro k hk
      simpa only [assignedCells, hk] using hxy.2 k hk
  rw [← hpre, (measurePreserving_splitAssignedCells m).measure_preimage hS.nullMeasurableSet,
    Measure.prod_apply hS, ← lintegral_indicator hs]
  apply lintegral_congr
  intro d
  by_cases hd : d ∈ s
  · rw [Set.indicator_of_mem hd]
    have he : Prod.mk d ⁻¹' S = univ.pi (noBlockCell m q d) := by
      ext z
      simp [S, hd]
    rw [he, Measure.pi_pi]
  · rw [Set.indicator_of_notMem hd]
    have he : Prod.mk d ⁻¹' S = ∅ := by
      ext z
      simp [S, hd]
    rw [he, measure_empty]

private theorem measureReal_noBlockCell_unmatched {n w : ℕ} (m : Matching n w) (q : ℝ)
    (d : Fin n → MarksCell) (e : OffAssignment m) (hq : q ∈ Icc (0 : ℝ) 1)
    (hu : ∀ k, m k ≠ e.val.2) :
    marksCellMeasure.real (noBlockCell m q d e) = 1 - q * (d e.val.1).1 := by
  let a : unitInterval :=
    ⟨q * (d e.val.1).1, mul_nonneg hq.1 (d e.val.1).1.property.1,
      (mul_le_of_le_one_left (d e.val.1).1.property.1 hq.2).trans (d e.val.1).1.property.2⟩
  have he : noBlockCell m q d e = (Iio a ×ˢ (univ : Set unitInterval))ᶜ := by
    ext z
    simp [noBlockCell, a, hu]
    rfl
  rw [he, measureReal_compl (measurableSet_Iio.prod MeasurableSet.univ),
    marksCellMeasure, probReal_univ, measureReal_prod_prod, probReal_univ, mul_one,
    measureReal_def, unitInterval.volume_Iio, ENNReal.toReal_ofReal a.property.1]

private theorem measureReal_noBlockCell_matched {n w : ℕ} (m : Matching n w) (q : ℝ)
    (d : Fin n → MarksCell) (e : OffAssignment m) (hq : q ∈ Icc (0 : ℝ) 1)
    (k : Fin n) (hk : m k = e.val.2) :
    marksCellMeasure.real (noBlockCell m q d e) = 1 - q ^ 2 * (d e.val.1).1 * (d k).2 := by
  let a : unitInterval :=
    ⟨q * (d e.val.1).1, mul_nonneg hq.1 (d e.val.1).1.property.1,
      (mul_le_of_le_one_left (d e.val.1).1.property.1 hq.2).trans (d e.val.1).1.property.2⟩
  let b : unitInterval :=
    ⟨q * (d k).2, mul_nonneg hq.1 (d k).2.property.1,
      (mul_le_of_le_one_left (d k).2.property.1 hq.2).trans (d k).2.property.2⟩
  have he : noBlockCell m q d e = (Iio a ×ˢ Iio b)ᶜ := by
    ext z
    have hy : (∀ l, m l = e.val.2 → (z.2 : ℝ) < q * (d l).2) ↔
        (z.2 : ℝ) < q * (d k).2 := by
      refine ⟨fun h ↦ h k hk, fun h l hl ↦ ?_⟩
      obtain rfl : l = k := m.injective (hl.trans hk.symm)
      exact h
    change (¬ ((z.1 : ℝ) < q * (d e.val.1).1 ∧
      ∀ k, m k = e.val.2 → (z.2 : ℝ) < q * (d k).2)) ↔
        ¬ ((z.1 : ℝ) < (a : ℝ) ∧ (z.2 : ℝ) < (b : ℝ))
    rw [hy]
  rw [he, measureReal_compl (measurableSet_Iio.prod measurableSet_Iio), marksCellMeasure,
    probReal_univ, measureReal_prod_prod]
  simp only [measureReal_def, unitInterval.volume_Iio, ENNReal.toReal_ofReal a.property.1,
    ENNReal.toReal_ofReal b.property.1]
  change 1 - (q * (d e.val.1).1) * (q * (d k).2) = _
  ring

private def columnLabel {n : ℕ} (m : Matching n (n + 1)) (u : Fin (n + 1)) :
    Option (Fin n) → Fin (n + 1)
  | none => u
  | some k => m k

private theorem columnLabel_bijective {n : ℕ} (m : Matching n (n + 1)) (u : Fin (n + 1))
    (hu : ∀ i, m i ≠ u) : Function.Bijective (columnLabel m u) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by simp⟩
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some j => exact (hu j h.symm).elim
  | some i =>
    cases b with
    | none => exact (hu i h).elim
    | some j => exact congrArg some (m.injective h)

private theorem offAssignment_product {n : ℕ} (m : Matching n (n + 1)) (u : Fin (n + 1))
    (hu : ∀ i, m i ≠ u) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (d : Fin n → MarksCell) :
    ∏ e : OffAssignment m, marksCellMeasure (noBlockCell m q d e) =
      ENNReal.ofReal ((∏ i : Fin n, (1 - q * (d i).1.val)) *
        ∏ i : Fin n, ∏ j ∈ Finset.univ.erase i, (1 - q ^ 2 * (d i).1.val * (d j).2.val)) := by
  let f (e : Fin n × Fin (n + 1)) : ℝ :=
    if h : e.2 ≠ m e.1 then marksCellMeasure.real (noBlockCell m q d ⟨e, h⟩) else 1
  have hprod : (∏ e : OffAssignment m, marksCellMeasure.real (noBlockCell m q d e)) =
      ∏ e : Fin n × Fin (n + 1), f e := by
    have h := Fintype.prod_subtype_mul_prod_subtype (fun e : Fin n × Fin (n + 1) ↦ e.2 ≠ m e.1) f
    have hleft (e : OffAssignment m) :
        f e.val = marksCellMeasure.real (noBlockCell m q d e) := dite_eq_left e.property
    have hright (e : {e : Fin n × Fin (n + 1) // ¬ e.2 ≠ m e.1}) :
        f e.val = 1 := dite_eq_right e.property
    simpa only [hleft, hright, Finset.prod_const_one, mul_one] using h
  have hrow (i : Fin n) : (∏ j : Fin (n + 1), f (i, j)) =
      (1 - q * (d i).1.val) * ∏ j ∈ Finset.univ.erase i, (1 - q ^ 2 * (d i).1.val * (d j).2.val) := by
    let e := Equiv.ofBijective (columnLabel m u) (columnLabel_bijective m u hu)
    rw [← e.prod_comp (fun j ↦ f (i, j)), Fintype.prod_option]
    change f (i, u) * (∏ j, f (i, m j)) = _
    have hv : f (i, u) = 1 - q * (d i).1.val := by
      simp only [f, dite_eq_left (hu i).symm]
      exact measureReal_noBlockCell_unmatched m q d ⟨(i, u), (hu i).symm⟩ hq hu
    rw [hv, ← Finset.filter_ne, Finset.prod_filter]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    by_cases hij : j ≠ i
    · have hm : m j ≠ m i := fun he ↦ hij (m.injective he)
      simp only [f, dite_eq_left hm, ite_eq_left (Ne.symm hij)]
      exact measureReal_noBlockCell_matched m q d ⟨(i, m j), hm⟩ hq j rfl
    · have he : j = i := not_ne_iff.mp hij
      subst j
      simp [f]
  rw [← ENNReal.ofReal_toReal (a := ∏ e : OffAssignment m, marksCellMeasure (noBlockCell m q d e))
    (ENNReal.prod_ne_top fun _ _ ↦ measure_ne_top _ _)]
  simp only [ENNReal.toReal_prod, ← measureReal_def, hprod, Fintype.prod_prod_type]
  simp_rw [hrow]
  rw [Finset.prod_mul_distrib]

/-- The exact joint law in the one-extra-worker market. Conditional on the assigned marks,
the vacancy contributes one factor per firm and each off-diagonal pair contributes one factor. -/
theorem marksProfileMeasure_stable_assignedCells {n : ℕ} (m : Matching n (n + 1))
    (u : Fin (n + 1)) (hu : ∀ i, m i ≠ u) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (s : Set (Fin n → MarksCell)) (hs : MeasurableSet s) :
    marksProfileMeasure n (n + 1)
      {p | MarksStable (fun i j ↦ (p i j).1.val) (fun i j ↦ (p i j).2.val) q m ∧
        assignedCells m p ∈ s} =
      ∫⁻ d in s, ENNReal.ofReal ((∏ i : Fin n, (1 - q * (d i).1.val)) *
        ∏ i : Fin n, ∏ j ∈ Finset.univ.erase i, (1 - q ^ 2 * (d i).1.val * (d j).2.val))
        ∂Measure.pi (fun _ : Fin n ↦ marksCellMeasure) := by
  rw [marksProfileMeasure_stable_assignedCells_eq_lintegral m q s hs]
  exact lintegral_congr (offAssignment_product m u hu q hq)

end WorkerCompromiseProof.Bounds
