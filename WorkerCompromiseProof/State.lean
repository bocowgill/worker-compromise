/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WorkerCompromiseProof.Core.RowEvents
public import WorkerCompromiseProof.Core.Realization
public import WorkerCompromiseProof.Core.TailIntegral

/-!
# Fixed partial assignments in the worker-tail argument

Only the partners on recorded firms matter. A total injection witnessing feasibility lets us
represent a partial assignment without making arbitrary choices of an outside option for a firm.
The accumulated mass uses the actual continuous marks in the recorded rows.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open SwitchingCostMatching MeasureTheory
open scoped Classical

/-- Recorded firms together with an injection agreeing with all their assigned partners. -/
structure Partial (n : ℕ) (u : Fin (n+1)) where
  rows : Finset (Fin n)
  assignment : Matching n (n+1)
  vacant : ∀ i, assignment i ≠ u

/-- An extension skips a row or names a worker other than the prescribed vacancy. -/
abbrev Label (n : ℕ) := Fin n → Option (Fin n)

def labelRows {n : ℕ} (F : Label n) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ (F i).isSome

theorem mem_labelRows_iff {n : ℕ} {F : Label n} {i : Fin n} :
    i ∈ labelRows F ↔ ∃ j, F i = some j := by
  cases h : F i <;> simp [labelRows, h]

namespace Partial

variable {n : ℕ} {u : Fin (n+1)}

def root (u : Fin (n+1)) : Partial n u :=
  ⟨∅, u.succAboveEmb, u.succAbove_ne⟩

def workers (P : Partial n u) := P.rows.image P.assignment

noncomputable def lower (P : Partial n u) (z : MarksProfile n (n+1)) (j : Fin (n+1)) : ℝ :=
  ∑ i ∈ P.rows, if P.assignment i = j then (z i j).2.val else 0

noncomputable def mass (P : Partial n u) (z : MarksProfile n (n+1)) : ℝ :=
  1 + ∑ i ∈ P.rows, (z i (P.assignment i)).2.val

@[simp] theorem mass_root (u : Fin (n+1)) (z : MarksProfile n (n+1)) :
    (root u).mass z = 1 := by simp [mass, root]

theorem vacancy_fresh (P : Partial n u) : u ∉ P.workers := by
  rintro hu
  obtain ⟨i, _, h⟩ := Finset.mem_image.mp hu
  exact P.vacant i h

theorem lower_assigned (P : Partial n u) (z : MarksProfile n (n+1)) {i : Fin n}
    (hi : i ∈ P.rows) : P.lower z (P.assignment i) = (z i (P.assignment i)).2.val := by
  classical
  simp [lower, P.assignment.injective.eq_iff, hi]

theorem lower_mem (P : Partial n u) (z : MarksProfile n (n+1)) {j : Fin (n+1)}
    (hj : j ∈ P.workers) : P.lower z j ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  rw [P.lower_assigned z hi]
  exact (z i (P.assignment i)).2.property

theorem mass_eq (P : Partial n u) (z : MarksProfile n (n+1)) :
    P.mass z = 1 + ∑ j ∈ P.workers, P.lower z j := by
  unfold mass workers
  rw [Finset.sum_image P.assignment.injective.injOn]
  exact congrArg (1 + ·) (Finset.sum_congr rfl fun i hi ↦ (P.lower_assigned z hi).symm)

theorem mass_ge_one (P : Partial n u) (z : MarksProfile n (n+1)) : 1 ≤ P.mass z := by
  unfold mass
  linarith [Finset.sum_nonneg (s := P.rows) (fun i _ ↦ (z i (P.assignment i)).2.property.1)]

theorem card_mul_le_mass (P : Partial n u) (z : MarksProfile n (n+1)) {b : ℝ}
    (h : ∀ i ∈ P.rows, b ≤ (z i (P.assignment i)).2.val) :
    (P.rows.card : ℝ)*b ≤ P.mass z := by
  have H : (P.rows.card : ℝ)*b ≤ ∑ i ∈ P.rows, (z i (P.assignment i)).2.val := by
    simpa using Finset.sum_le_sum h
  unfold mass
  linarith

theorem mass_sub_one_le_tail (P : Partial n u) (z : MarksProfile n (n+1))
    (m : Matching n (n+1)) {cutoff : ℝ}
    (hagree : ∀ i ∈ P.rows, m i = P.assignment i)
    (hmark : ∀ i ∈ P.rows, cutoff ≤ (z i (P.assignment i)).2.val) :
    P.mass z - 1 ≤ workerTailMass cutoff (fun i ↦ (z i (m i)).2.val) := by
  classical
  unfold mass workerTailMass
  rw [add_sub_cancel_left]
  refine (le_of_eq (Finset.sum_congr rfl fun i hi ↦ ?_)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_)
  · simp only [hagree i hi, ite_eq_left (hmark i hi)]
  · intro i _ _
    split_ifs
    · exact (z i (m i)).2.property.1
    · exact le_rfl

/-- The newly named rows are unused and their specified partners admit an injective extension. -/
def Valid (P : Partial n u) (F : Label n) : Prop :=
  Disjoint P.rows (labelRows F) ∧ ∃ m : Matching n (n+1), (∀ i, m i ≠ u) ∧
    (∀ i ∈ P.rows, m i = P.assignment i) ∧ (∀ i j, F i = some j → m i = u.succAbove j)

noncomputable def extend (P : Partial n u) (F : Label n) (h : P.Valid F) : Partial n u :=
  ⟨P.rows ∪ labelRows F, h.2.choose, h.2.choose_spec.1⟩

@[simp] theorem extend_rows (P : Partial n u) (F : Label n) (h : P.Valid F) :
    (P.extend F h).rows = P.rows ∪ labelRows F := rfl

theorem extend_old (P : Partial n u) {F : Label n} (h : P.Valid F) {i : Fin n}
    (hi : i ∈ P.rows) : (P.extend F h).assignment i = P.assignment i :=
  h.2.choose_spec.2.1 i hi

theorem extend_new (P : Partial n u) {F : Label n} (h : P.Valid F) {i j : Fin n}
    (hi : F i = some j) : (P.extend F h).assignment i = u.succAbove j :=
  h.2.choose_spec.2.2 i j hi

theorem fresh_of_valid (P : Partial n u) {F : Label n} (h : P.Valid F) {i j : Fin n}
    (hi : F i = some j) : u.succAbove j ∉ insert u P.workers := by
  classical
  intro hj
  rcases Finset.mem_insert.mp hj with hju | hj
  · exact u.succAbove_ne j hju
  obtain ⟨k, hk, hk'⟩ := Finset.mem_image.mp hj
  have heq : (P.extend F h).assignment k = (P.extend F h).assignment i := by
    rw [P.extend_old h hk, P.extend_new h hi, hk']
  have hki := (P.extend F h).assignment.injective heq
  exact Finset.disjoint_left.mp h.1 hk (hki ▸ mem_labelRows_iff.mpr ⟨j, hi⟩)

theorem extend_mass (P : Partial n u) {F : Label n} (h : P.Valid F)
    (z : MarksProfile n (n+1)) :
    (P.extend F h).mass z =
      P.mass z + ∑ i ∈ labelRows F, (z i ((P.extend F h).assignment i)).2.val := by
  unfold mass
  rw [extend_rows, Finset.sum_union h.1, ← add_assoc]
  congr 1
  exact congrArg (1 + ·) (Finset.sum_congr rfl fun i hi ↦ by rw [P.extend_old h hi])

/-- The exact partial mass depends only on recorded rows. -/
theorem mass_congr (P : Partial n u) {x y : MarksProfile n (n+1)}
    (h : ∀ i ∈ P.rows, x i = y i) : P.mass x = P.mass y :=
  congrArg (1 + ·) (Finset.sum_congr rfl fun i hi ↦ by rw [h i hi])

theorem lower_congr (P : Partial n u) {x y : MarksProfile n (n+1)}
    (h : ∀ i ∈ P.rows, x i = y i) : P.lower x = P.lower y := by
  funext j
  exact Finset.sum_congr rfl fun i hi ↦ by rw [h i hi]

/-- Each named row adds exactly its assigned mark. The remaining rows contribute zero. -/
theorem extend_mass_option (P : Partial n u) {F : Label n} (h : P.Valid F)
    (z : MarksProfile n (n+1)) :
    (P.extend F h).mass z = P.mass z +
      ∑ i, (F i).elim 0 (fun j ↦ (z i (u.succAbove j)).2.val) := by
  classical
  rw [P.extend_mass h]
  congr 1
  rw [labelRows, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases hi : F i with
  | none => simp
  | some j => simp [P.extend_new h hi]

end Partial
end WorkerCompromiseProof.Bounds.Paper
