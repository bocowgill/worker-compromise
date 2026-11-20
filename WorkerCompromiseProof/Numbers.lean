/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WorkerCompromiseProof.State

/-!
# Numerical bounds for a live partial assignment

Previously recorded marks all exceed the current scale. If their total mass
is below the stopping value, at least half of the firms remain available.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

/-- The bounds on the unused population, total mass and relative scale at a nonterminal stage. -/
theorem paper_screen_inputs {n : ℕ} {u : Fin (n+1)} (P : Partial n u)
    (z : MarksProfile n (n+1)) {b stop : ℝ} (hb : 0 < b)
    (hmark : ∀ i ∈ P.rows, b ≤ (z i (P.assignment i)).2.val) (hlive : P.mass z < stop)
    (hcap : stop / b ≤ (n : ℝ) / 2) (hscale : 1024 ≤ b⁻¹) :
    (n : ℝ) / 2 ≤ ((Finset.univ \ P.rows).card : ℝ) ∧ P.mass z ≤ (n : ℝ) * b ∧
      1024 ≤ P.mass z / b := by
  have hupper := (div_le_iff₀ hb).mp hcap
  have hrows : (P.rows.card : ℝ) ≤ (n : ℝ) / 2 := by
    apply le_of_mul_le_mul_right _ hb
    linarith only [P.card_mul_le_mass z hmark, hlive, hupper]
  constructor
  · have hnc : P.rows.card ≤ n := by simpa using Finset.card_le_univ P.rows
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    push_cast [hnc]
    linarith only [hrows]
  constructor
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by positivity) hb.le]
  · rw [div_eq_mul_inv]
    calc
      1024 ≤ b⁻¹ := hscale
      _ ≤ P.mass z * b⁻¹ := le_mul_of_one_le_left (inv_nonneg.mpr hb.le) (P.mass_ge_one z)

end WorkerCompromiseProof.Bounds.Paper
