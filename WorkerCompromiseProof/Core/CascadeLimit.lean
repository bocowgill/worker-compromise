/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib
public import WorkerCompromiseProof.Core.SwitchingCostMatching
public import WorkerCompromiseProof.Core.Realization
public import WorkerCompromiseProof.Core.RowEvents
public import WorkerCompromiseProof.Core.TailIntegral

/-!
# Measurable events of a violating stable assignment
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds

open Filter MeasureTheory SwitchingCostMatching
open scoped ENNReal Topology

/-- Some stable assignment has less than the required worker-mark tail mass. -/
def smallWorkerTailEvent (n : ℕ) (q cutoff stop : ℝ) : Set (MarksProfile n (n + 1)) :=
  {x | ∃ m : Matching n (n + 1),
    MarksStable (fun i j ↦ (x i j).1.val) (fun i j ↦ (x i j).2.val) q m ∧
      workerTailMass cutoff (fun i ↦ (x i (m i)).2.val) < stop - 1}

/-- Stability of a fixed injection is a measurable event in the product mark model. -/
theorem measurableSet_marksStable {n w : ℕ} (m : Matching n w) (q : ℝ) :
    MeasurableSet {x : MarksProfile n w | MarksStable
      (fun i j ↦ (x i j).1.val) (fun i j ↦ (x i j).2.val) q m} := by
  unfold MarksStable
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  by_cases hj : j = m i
  · simp [hj]
  · have hW : MeasurableSet {x : MarksProfile n w |
          ∀ k, m k = j → (x i j).2.val < q * (x k j).2.val} := by
      rw [Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro k
      by_cases hk : m k = j
      · simpa only [hk, true_implies] using
          (measurableSet_lt (by fun_prop) (by fun_prop) : MeasurableSet
            {x : MarksProfile n w | (x i j).2.val < q * (x k j).2.val})
      · simp [hk]
    have hF : MeasurableSet {x : MarksProfile n w |
        (x i j).1.val < q * (x i (m i)).1.val} := measurableSet_lt (by fun_prop) (by fun_prop)
    have hC : {x : MarksProfile n w | j ≠ m i →
        (x i j).1.val < q * (x i (m i)).1.val →
            ¬ (∀ k, m k = j → (x i j).2.val < q * (x k j).2.val)} =
        ({x : MarksProfile n w | (x i j).1.val < q * (x i (m i)).1.val} ∩
          {x : MarksProfile n w | ∀ k, m k = j → (x i j).2.val < q * (x k j).2.val})ᶜ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_inter_iff, not_and]
      exact ⟨fun h ↦ h hj, fun h _ ↦ h⟩
    rw [hC]
    exact (hF.inter hW).compl

/-- The worker-mark tail mass of a fixed assignment is measurable in the mark profile. -/
theorem measurable_assignedWorkerTailMass {n w : ℕ} (m : Matching n w) (cutoff : ℝ) :
    Measurable (fun x : MarksProfile n w ↦
      workerTailMass cutoff (fun i ↦ (x i (m i)).2.val)) := by
  refine (measurable_workerTailMass cutoff).comp (measurable_pi_iff.mpr ?_)
  intro i
  fun_prop

end WorkerCompromiseProof.Bounds
