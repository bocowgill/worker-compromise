/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WorkerCompromiseProof.Cover
public import WorkerCompromiseProof.Reveal

/-!
# Invariants for the next scale

For a retained extension, the old rows keep their assigned marks and the new pairs
contribute their actual marks. These facts supply the induction hypotheses at the next scale.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

variable {n : ℕ} {u : Fin (n+1)}

/-- The retained event requires the recorded mass to grow by the specified factor. -/
theorem retained_child_growth (P : Partial n u) (z : MarksProfile n (n+1))
    (F : Label n) (hF : P.Valid F) {x : MarksProfile n (n+1)} {q t b : ℝ}
    (hx : x ∈ retained P z F q t b hF) :
    (129/128 : ℝ) * P.mass z ≤ (P.extend F hF).mass x :=
  hx.2

/-- Every assigned mark in the extended partial assignment is large enough for the next scale. -/
theorem retained_child_marks (P : Partial n u) (z : MarksProfile n (n+1))
    (F : Label n) (hF : P.Valid F) {x : MarksProfile n (n+1)} {q t b : ℝ} (hb : 0 ≤ b)
    (hxz : ∀ i ∈ P.rows, x i = z i)
    (hmark : ∀ i ∈ P.rows, b ≤ (z i (P.assignment i)).2.val)
    (hx : x ∈ retained P z F q t b hF) :
    ∀ i ∈ (P.extend F hF).rows, b/8192 ≤ (x i ((P.extend F hF).assignment i)).2.val := by
  intro i hi
  refine (div_le_self hb (by norm_num : (1 : ℝ) ≤ 8192)).trans ?_
  rw [P.extend_rows F hF] at hi
  rcases Finset.mem_union.mp hi with hi | hi
  · rw [P.extend_old hF hi, hxz i hi]
    exact hmark i hi
  · obtain ⟨j, hij⟩ := mem_labelRows_iff.mp hi
    rw [P.extend_new hF hij]
    exact (hx.1 i j hij).2.2.le

end WorkerCompromiseProof.Bounds.Paper
