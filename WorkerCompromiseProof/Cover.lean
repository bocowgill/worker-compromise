/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WorkerCompromiseProof.State
public import WorkerCompromiseProof.Core.CascadeLimit

/-!
# A cover of all small-tail stable completions

For a fixed partial assignment the matching in the exceptional event is existential.
Its partners on the forced rows supply one of the finitely many labels. Only marked
conditions on named rows are retained for that label.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory SwitchingCostMatching
open scoped Classical

variable {n : ℕ} {u : Fin (n+1)}

/-- There is a small-tail stable completion of the fixed pairs with vacancy `u`. -/
def badCompletion (P : Partial n u) (q cutoff stop : ℝ) : Set (MarksProfile n (n+1)) :=
  {x | ∃ m : Matching n (n+1), (∀ i, m i ≠ u) ∧
    (∀ i ∈ P.rows, m i = P.assignment i) ∧
    MarksStable (fun i j ↦ (x i j).1.val) (fun i j ↦ (x i j).2.val) q m ∧
    workerTailMass cutoff (fun i ↦ (x i (m i)).2.val) < stop - 1}

theorem measurableSet_badCompletion (P : Partial n u) (q cutoff stop : ℝ) :
    MeasurableSet (badCompletion P q cutoff stop) := by
  unfold badCompletion
  rw [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun m ↦ ?_
  simp only [Set.ofPred_and]
  exact MeasurableSet.inter (MeasurableSet.const _)
    (MeasurableSet.inter (MeasurableSet.const _) ((measurableSet_marksStable m q).inter
      (measurableSet_lt (measurable_assignedWorkerTailMass m cutoff) measurable_const)))

/-- The fixed label's retained tests and growth check, before any probabilities are taken. -/
def retained (P : Partial n u) (z : MarksProfile n (n+1)) (F : Label n)
    (q t b : ℝ) (hF : P.Valid F) : Set (MarksProfile n (n+1)) :=
  {x | (∀ i j, F i = some j → x i ∈ tight u P.workers (P.lower z) q t ∧
      (x i (u.succAbove j)).1.val ≤ t ∧ b < (x i (u.succAbove j)).2.val) ∧
    (129/128 : ℝ) * P.mass z ≤ (P.extend F hF).mass x}

theorem measurableSet_retained (P : Partial n u) (z : MarksProfile n (n+1)) (F : Label n)
    (q t b : ℝ) (hF : P.Valid F) : MeasurableSet (retained P z F q t b hF) := by
  unfold retained
  rw [Set.ofPred_and]
  apply MeasurableSet.inter
  · rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun i ↦ ?_
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun j ↦ ?_
    by_cases hj : F i = some j
    · simp only [hj, true_implies, Set.ofPred_and]
      exact ((measurable_pi_apply i) (measurableSet_tight ..)).inter
        ((measurableSet_le (by fun_prop) measurable_const).inter
          (measurableSet_lt measurable_const (by fun_prop)))
    · simp [hj]
  · exact measurableSet_le measurable_const (by unfold Partial.mass; fun_prop)

theorem retained_congr (P : Partial n u) (z : MarksProfile n (n+1)) (F : Label n)
    (q t b : ℝ) (hF : P.Valid F) {x y : MarksProfile n (n+1)}
    (hxy : ∀ i ∈ P.rows ∪ labelRows F, x i = y i) :
    x ∈ retained P z F q t b hF ↔ y ∈ retained P z F q t b hF := by
  have hrow (i j) (h : F i = some j) : x i = y i :=
    hxy i (Finset.mem_union_right _ (mem_labelRows_iff.mpr ⟨j, h⟩))
  have hmass : (P.extend F hF).mass x = (P.extend F hF).mass y := by
    unfold Partial.mass
    congr 1
    exact Finset.sum_congr rfl fun i hi ↦ by rw [hxy i hi]
  constructor <;> rintro ⟨h, hD⟩
  · exact ⟨fun i j hij ↦ (hrow i j hij) ▸ h i j hij, hmass ▸ hD⟩
  · exact ⟨fun i j hij ↦ (hrow i j hij).symm ▸ h i j hij, hmass.symm ▸ hD⟩

/-- Sufficient recorded mass rules out any violating completion on the frozen rows. -/
theorem not_badCompletion_of_mass (P : Partial n u) (z : MarksProfile n (n+1))
    {x : MarksProfile n (n+1)} {q cutoff stop : ℝ}
    (hxz : ∀ i ∈ P.rows, x i = z i)
    (hy : ∀ i ∈ P.rows, cutoff ≤ (z i (P.assignment i)).2.val) (hD : stop ≤ P.mass z) :
    x ∉ badCompletion P q cutoff stop := by
  rintro ⟨m, _, hm, _, htail⟩
  have hx : ∀ i ∈ P.rows, cutoff ≤ (x i (P.assignment i)).2.val :=
    fun i hi ↦ (hxz i hi).symm ▸ hy i hi
  have heq : P.mass x = P.mass z :=
    congrArg (1 + ·) (Finset.sum_congr rfl fun i hi ↦ by rw [hxz i hi])
  have h := P.mass_sub_one_le_tail x m hm hx
  linarith

/-- A violating completion either has few forced rows or supplies a feasible retained
label and remains a violating completion of that extension. -/
theorem badCompletion_cover (P : Partial n u) (z : MarksProfile n (n+1))
    {x : MarksProfile n (n+1)} {q t b cutoff stop : ℝ} (hq : 0 < q) (hb : 0 < b)
    (hxz : ∀ i ∈ P.rows, x i = z i) (hx : x ∈ badCompletion P q cutoff stop) :
    (((Finset.univ \ P.rows).filter (fun i ↦ x i ∈
      forcedRowsEvent u P.workers (P.lower z) q t b)).card : ℝ) < P.mass z / (128*b) ∨
    ∃ (F : Label n) (hF : P.Valid F), x ∈ retained P z F q t b hF ∧
      x ∈ badCompletion (P.extend F hF) q cutoff stop := by
  let I := (Finset.univ \ P.rows).filter fun i ↦ x i ∈ forcedRowsEvent u P.workers (P.lower z) q t b
  by_cases hsize : (I.card : ℝ) < P.mass z / (128*b)
  · exact Or.inl hsize
  right
  obtain ⟨m, hu, ha, hs, htail⟩ := hx
  have old (i : Fin n) : m i ∈ P.workers ↔ i ∈ P.rows := by
    constructor
    · intro hj
      obtain ⟨k, hk, h⟩ := Finset.mem_image.mp hj
      have hki := m.injective ((ha k hk).trans h)
      exact hki ▸ hk
    · intro hi
      exact Finset.mem_image.mpr ⟨i, hi, (ha i hi).symm⟩
  have hworkers (j) (hj : j ∈ P.workers) : ∃ k, m k = j := by
    obtain ⟨k, hk, h⟩ := Finset.mem_image.mp hj
    exact ⟨k,(ha k hk).trans h⟩
  have hmarks (k) (hk : m k ∈ P.workers) : P.lower z (m k) ≤ (x k (m k)).2.val := by
    have hi := (old k).mp hk
    rw [ha k hi, P.lower_assigned z hi, hxz k hi]
  have forced (i) (hi : i ∈ I) : (x i (m i)).1.val ≤ t ∧ b < (x i (m i)).2.val := by
    obtain ⟨hold, h1, h2⟩ := Finset.mem_filter.mp hi
    exact forcedRow_assigned hq hs hu hworkers hmarks
      (fun h ↦ (Finset.mem_sdiff.mp hold).2 ((old i).mp h))
      ((mem_tight P.vacancy_fresh).mp h1) (mem_noGood.mp h2)
  choose j hj using fun i ↦ Fin.exists_succAbove_eq (hu i)
  let F : Label n := fun i ↦ if i ∈ I then some (j i) else none
  have memF (i k) (h : F i = some k) : i ∈ I ∧ j i = k := by
    by_cases hi : i ∈ I <;> simp_all [F]
  have rowsF : labelRows F = I := by
    ext i
    simp [labelRows, F, apply_ite]
  have matchF (i k) (h : F i = some k) : m i = u.succAbove k := by
    rw [← (memF i k h).2, hj i]
  have hF : P.Valid F := by
    refine ⟨?_, m, hu, ha, matchF⟩
    rw [rowsF, Finset.disjoint_left]
    exact fun i hi hiI ↦ (Finset.mem_sdiff.mp (Finset.mem_filter.mp hiI).1).2 hi
  have hn (i) (hi : i ∈ I) : (P.extend F hF).assignment i = m i := by
    have he : F i = some (j i) := by simp [F, hi]
    exact (P.extend_new hF he).trans (hj i)
  refine ⟨F, hF, ⟨?_, ?_⟩, m, hu, ?_, hs, htail⟩
  · intro i k h
    obtain ⟨hi, _⟩ := memF i k h
    rw [← matchF i k h]
    exact ⟨(Finset.mem_filter.mp hi).2.1, forced i hi⟩
  · have hsum : (I.card : ℝ) * b ≤ ∑ i ∈ I, (x i ((P.extend F hF).assignment i)).2.val := by
      simpa [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum (s := I) (f := fun _ ↦ b)
        (g := fun i ↦ (x i ((P.extend F hF).assignment i)).2.val)
        (fun i hi ↦ (hn i hi).symm ▸ (forced i hi).2.le)
    have hm : P.mass x = P.mass z := congrArg (1 + ·)
      (Finset.sum_congr rfl fun i hi ↦ by rw [hxz i hi])
    rw [P.extend_mass hF, rowsF, hm]
    have hbnd := (div_le_iff₀ (show 0 < 128*b by positivity)).mp (le_of_not_gt hsize)
    linarith
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (ha i hi).trans (P.extend_old hF hi).symm
    · exact (hn i (rowsF ▸ hi)).symm

end WorkerCompromiseProof.Bounds.Paper
