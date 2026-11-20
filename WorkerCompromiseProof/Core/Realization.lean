/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib
public import WorkerCompromiseProof.Core.SwitchingCostMatching

/-!
# Deterministic restrictions imposed by stability
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds

open SwitchingCostMatching

/-- Stability expressed with firm and worker tail marks and the discount $q=e^{-\varepsilon}$. -/
def MarksStable {n w : ℕ} (X Y : Fin n → Fin w → ℝ) (q : ℝ)
    (m : Matching n w) : Prop :=
  ∀ i j, j ≠ m i → X i j < q * X i (m i) →
    ¬ (∀ k, m k = j → Y i j < q * Y k j)

private theorem exp_neg_lt_discount_iff (u u' ε : ℝ) :
    Real.exp (-u') < Real.exp (-ε) * Real.exp (-u) ↔ u + ε < u' := by
  rw [← Real.exp_add, Real.exp_lt_exp]
  constructor <;> intro h <;> linarith

/-- The raw utility model and its exponential mark formulation have the same stable matchings. -/
theorem marksStable_exp_neg_iff {n w : ℕ} (p : Profile n w) (ε : ℝ)
    (m : Matching n w) :
    MarksStable
        (fun i j ↦ Real.exp (-p (false, i, j)))
        (fun i j ↦ Real.exp (-p (true, i, j))) (Real.exp (-ε)) m ↔
      IsStable p ε m := by
  simp only [MarksStable, IsStable, IsBlockingPair, exp_neg_lt_discount_iff]
  constructor
  · intro h i j hblock
    exact h i j hblock.1 hblock.2.1 hblock.2.2
  · intro h i j hij hfirm hworker
    exact h i j ⟨hij, hfirm, hworker⟩

/-- An injection into one extra worker leaves a worker unmatched. -/
theorem exists_unmatched {n : ℕ} (m : Matching n (n + 1)) :
    ∃ u, ∀ k, m k ≠ u := by
  by_contra! h
  have hc := Fintype.card_le_of_surjective m h
  simp at hc

/-- A forced unused firm must take a fresh worker with firm mark at most $t$ and worker mark
strictly above $b$. The earlier workers are recorded with valid lower marks $v$. -/
theorem forcedRow_assigned {n w : ℕ} {X Y : Fin n → Fin w → ℝ}
    {q t b : ℝ} {m : Matching n w} {i : Fin n} {u : Fin w}
    {J : Finset (Fin w)} {v : Fin w → ℝ}
    (hq : 0 < q) (hm : MarksStable X Y q m) (hu : ∀ k, m k ≠ u)
    (hJ : ∀ j ∈ J, ∃ k, m k = j) (hv : ∀ k, m k ∈ J → v (m k) ≤ Y k (m k))
    (hi : m i ∉ J)
    (htight : X i u < q * t ∨ ∃ j ∈ J, X i j < q * t ∧ Y i j < q * v j)
    (hnoGood : ∀ j, j ≠ u → j ∉ J → ¬ (X i j ≤ t ∧ Y i j ≤ b)) :
    X i (m i) ≤ t ∧ b < Y i (m i) := by
  have hX : X i (m i) ≤ t := by
    by_contra! ht
    have hqt : q * t < q * X i (m i) := mul_lt_mul_of_pos_left ht hq
    rcases htight with h | ⟨j, hj, hXj, hYj⟩
    · exact hm i u (Ne.symm (hu i)) (h.trans hqt) (fun k hk ↦ (hu k hk).elim)
    · have hji : j ≠ m i := by
        rintro rfl
        exact hi hj
      obtain ⟨k, hk⟩ := hJ j hj
      subst j
      apply hm i (m k) hji (hXj.trans hqt)
      intro l hl
      have hlk : l = k := m.injective hl
      subst l
      exact hYj.trans_le (mul_le_mul_of_nonneg_left (hv k hj) hq.le)
  exact ⟨hX, lt_of_not_ge (fun hY ↦ hnoGood (m i) (hu i) hi ⟨hX, hY⟩)⟩

end WorkerCompromiseProof.Bounds
