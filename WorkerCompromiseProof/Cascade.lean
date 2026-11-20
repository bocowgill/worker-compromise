/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WorkerCompromiseProof.Induction

/-!
# The finite worker-tail bound, simultaneously over the entire stable set

Every stable injection has an unmatched worker. For each possible vacancy apply backward
induction at the empty partial assignment. Summing this error over the vacancy labels gives
the paper's finite bound without restricting how a clearinghouse selects an assignment.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory SwitchingCostMatching
open scoped ENNReal

/-- Probability that even one stable assignment violates the worker-tail requirement. -/
theorem measure_exists_stable_smallWorkerTail_le {n L : ℕ} (b : ℕ → ℝ)
    {q stop cutoff : ℝ} (hn : 2 ≤ n) (hq : q ∈ Set.Icc (1/2 : ℝ) 1)
    (hstop : stop ≤ (129 / 128 : ℝ)^L)
    (hb : ∀ l ≤ L, 0 < b l) (hnext : ∀ l < L, b (l+1) = b l / 8192)
    (hcut : ∀ l ≤ L, cutoff ≤ b l)
    (hnum : ∀ l < L, b l ≤ 1 ∧ 1 ≤ (n : ℝ)*b l ∧
      stop / b l ≤ (n : ℝ)/2 ∧ 1024 ≤ (b l)⁻¹) :
    marksProfileMeasure n (n+1) {x | ∃ m : Matching n (n+1),
      MarksStable (fun i j ↦ (x i j).1.val) (fun i j ↦ (x i j).2.val) q m ∧
      (∑ i : Fin n, if cutoff ≤ (x i (m i)).2.val then (x i (m i)).2.val else 0) < stop - 1}
      ≤ (n+1 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-1 / (1024*b 0))) := by
  classical
  let μ := marksProfileMeasure n (n+1)
  let B (u : Fin (n+1)) := badCompletion (Partial.root u) q cutoff stop
  let e := ENNReal.ofReal (Real.exp (-1 / (1024 * b 0)))
  have hB (u : Fin (n+1)) : μ (B u) ≤ e := by
    let z : MarksProfile n (n+1) := fun _ _ ↦ 0
    have h := measure_badCompletion_le b hn hq hstop hb hnext hcut hnum (l := 0)
      (Nat.zero_le L) (Partial.root u) z (by simp [Partial.root]) (by simp)
    have hfreeze : freezeRows (Partial.root u).rows z = id := by
      funext x i
      simp [Partial.root, freezeRows]
    rw [hfreeze, Set.preimage_id] at h
    simpa only [Partial.mass_root] using h
  have hsum : (∑ u, μ (B u)) ≤ (n+1 : ℝ≥0∞)*e := by
    simpa [nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) (fun u _ ↦ hB u)
  apply (measure_mono (t := ⋃ u, B u) ?_).trans ((measure_iUnion_fintype_le μ B).trans hsum)
  rintro x ⟨m, hm, htail⟩
  obtain ⟨u, hu⟩ := exists_unmatched m
  exact Set.mem_iUnion.mpr ⟨u, m, hu, by simp [Partial.root], hm, htail⟩

end WorkerCompromiseProof.Bounds.Paper
