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
# Assignments with large firm scores and a heavy worker tail
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds

open MeasureTheory Set SwitchingCostMatching Filter
open scoped ENNReal BigOperators

/-- Some stable injection has both a large sum of assigned firm marks and a heavy worker tail. -/
def largeFirmScoreHeavyWorkerTail (n : ℕ) (q s b B : ℝ) : Set (MarksProfile n (n + 1)) :=
  {p | ∃ m : Matching n (n + 1),
    MarksStable (fun i j ↦ (p i j).1.val) (fun i j ↦ (p i j).2.val) q m ∧
    s ≤ (∑ i, (p i (m i)).1.val) ∧ B ≤ workerTailMass b (fun i ↦ (p i (m i)).2.val)}

end WorkerCompromiseProof.Bounds
