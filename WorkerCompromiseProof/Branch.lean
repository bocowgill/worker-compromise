/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WorkerCompromiseProof.Cover
public import WorkerCompromiseProof.Reveal
public import WorkerCompromiseProof.RowWeight

/-!
# Paying for a fixed set of newly named partners

Only the named rows must pass the retained tests. After revealing those rows, the probability
bound for a completion of the extended assignment can be integrated against their actual marks.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory
open scoped ENNReal Classical

variable {n : ℕ} {u : Fin (n+1)}

/-- A row can name a fresh partner only if the row itself has not been used. -/
noncomputable def choiceWeight (P : Partial n u) (z : MarksProfile n (n+1)) (q t b : ℝ)
    (i j : Fin n) (r : MarksRow (n+1)) : ℝ≥0∞ :=
  if i ∈ P.rows ∨ u.succAbove j ∈ P.workers then 0
  else rowWeight u P.workers (P.lower z) q t b (u.succAbove j) r

@[fun_prop]
theorem measurable_choiceWeight (P : Partial n u) (z : MarksProfile n (n+1)) (q t b : ℝ)
    (i j : Fin n) : Measurable (choiceWeight P z q t b i j) := by
  change Measurable (fun r ↦ choiceWeight P z q t b i j r)
  by_cases h : i ∈ P.rows ∨ u.succAbove j ∈ P.workers
  · simpa only [choiceWeight, ite_eq_left h] using
      (measurable_const : Measurable (fun _ : MarksRow (n+1) ↦ (0 : ℝ≥0∞)))
  · simpa only [choiceWeight, ite_eq_right h] using
      measurable_rowWeight u P.workers (P.lower z) q t b (u.succAbove j)

theorem lintegral_choiceWeight_le (P : Partial n u) (z : MarksProfile n (n+1))
    (i j : Fin n) {q t b : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hb : 0 < b) :
    (∫⁻ r, choiceWeight P z q t b i j r ∂marksRowMeasure (n+1)) ≤
      ENNReal.ofReal (t^2 * P.mass z * b / 8) := by
  by_cases h : i ∈ P.rows ∨ u.succAbove j ∈ P.workers
  · simp [choiceWeight, h]
  · simpa only [choiceWeight, ite_eq_right h, P.mass_eq z] using
      lintegral_rowWeight_le P.vacancy_fresh
        (fun hj ↦ (Finset.mem_insert.mp hj).elim (u.succAbove_ne j) (fun hj' ↦ h (Or.inr hj')))
        hq ht hb (fun _ hj ↦ P.lower_mem z hj)

private theorem exp_next_eq (D b : ℝ) (m : Fin n → ℝ) :
    ENNReal.ofReal (Real.exp (-(D + ∑ i, m i) / (1024 * (b / 8192)))) =
      ENNReal.ofReal (Real.exp (-8 * D / b)) *
        ∏ i, ENNReal.ofReal (Real.exp (-8 * m i / b)) := by
  have h : -(D + ∑ i, m i) / (1024 * (b / 8192)) =
      (-8 * D / b) + ∑ i, -8 * m i / b := by
    simp only [← Finset.sum_div, ← Finset.mul_sum]
    ring
  rw [h, Real.exp_add, Real.exp_sum, ENNReal.ofReal_mul (Real.exp_nonneg _),
    ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ Real.exp_nonneg _)]

/-- Averaging the child induction bound for one fixed injective label. -/
theorem measure_branch_le (P : Partial n u) (z : MarksProfile n (n+1)) (F : Label n)
    (q t b cutoff stop : ℝ) (hF : P.Valid F)
    (hchild : ∀ x, freezeRows P.rows z x ∈ retained P z F q t b hF →
      marksProfileMeasure n (n+1)
        ((freezeRows (P.extend F hF).rows (freezeRows P.rows z x)) ⁻¹'
          badCompletion (P.extend F hF) q cutoff stop) ≤
        ENNReal.ofReal (Real.exp (-((P.extend F hF).mass (freezeRows P.rows z x)) /
          (1024 * (b/8192))))) :
    marksProfileMeasure n (n+1) ((freezeRows P.rows z) ⁻¹'
      (retained P z F q t b hF ∩ badCompletion (P.extend F hF) q cutoff stop)) ≤
      ENNReal.ofReal (Real.exp (-8 * P.mass z / b)) *
        ∫⁻ x, ∏ i, (F i).elim 1 (fun j ↦ choiceWeight P z q t b i j (x i))
          ∂marksProfileMeasure n (n+1) := by
  let A := retained P z F q t b hF
  let B := badCompletion (P.extend F hF) q cutoff stop
  let bound := fun x ↦ ENNReal.ofReal (Real.exp (-((P.extend F hF).mass x) / (1024*(b/8192))))
  have h := measure_revealRows_le (marksRowMeasure (n+1)) P.rows (labelRows F) z A B bound
    (measurableSet_retained P z F q t b hF)
    (measurableSet_badCompletion (P.extend F hF) q cutoff stop)
    (fun _ _ hxy ↦ retained_congr P z F q t b hF hxy) hchild
  change marksProfileMeasure n (n+1) ((freezeRows P.rows z) ⁻¹' (A ∩ B)) ≤
    ∫⁻ x, A.indicator bound (freezeRows P.rows z x) ∂marksProfileMeasure n (n+1) at h
  refine h.trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  let v := freezeRows P.rows z x
  change A.indicator bound v ≤ _
  by_cases hv : v ∈ A
  · rw [Set.indicator_of_mem hv]
    change ENNReal.ofReal (Real.exp (-((P.extend F hF).mass v) / (1024 * (b/8192)))) ≤ _
    have hmass : P.mass v = P.mass z :=
      P.mass_congr (fun i hi ↦ by simp [v, freezeRows, hi])
    rw [P.extend_mass_option hF v, hmass, exp_next_eq]
    apply le_of_eq
    congr 1
    refine Finset.prod_congr rfl (fun i _ ↦ ?_)
    cases hFi : F i with
    | none => simp
    | some j =>
      have hrow : i ∉ P.rows := fun hi ↦
        Finset.disjoint_left.mp hF.1 hi (mem_labelRows_iff.mpr ⟨j,hFi⟩)
      have hworker : u.succAbove j ∉ P.workers :=
        fun hj ↦ P.fresh_of_valid hF hFi (Finset.mem_insert_of_mem hj)
      have htests := hv.1 i j hFi
      have heq : v i = x i := by simp [v, freezeRows, hrow]
      rw [heq] at htests ⊢
      simp [choiceWeight, rowWeight, hrow, hworker, htests]
  · rw [Set.indicator_of_notMem hv]
    exact bot_le

end WorkerCompromiseProof.Bounds.Paper
