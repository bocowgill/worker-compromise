/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WorkerCompromiseProof.Core.CascadeLimit
public import WorkerCompromiseProof.Count
public import WorkerCompromiseProof.Core.Welfare

/-!
# The firm score in the three-page proof

A single stable witness for an excessive firm score either violates the uniform
worker-tail bound or contributes to the count of stable assignments having both
an excessive firm score and a large worker tail. This reduction transports both
events through the uniform-mark representation before taking probabilities.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open Filter MeasureTheory SwitchingCostMatching
open scoped ENNReal Topology

/-- A firm-score violation in the exponential market is charged to one of two
events on uniform marks. Both events allow the injection to depend on the market. -/
theorem measure_largeFirmScore_le_tail_add_heavy (n : ℕ) (s b stop : ℝ) :
    profileMeasureWithWorkers n (n + 1) (Imbalanced.compromiseLargeScore n s) ≤
      marksProfileMeasure n (n + 1) (smallWorkerTailEvent n (compromiseQ n) b stop) +
      marksProfileMeasure n (n + 1) (largeFirmScoreHeavyWorkerTail n (compromiseQ n) s b (stop - 1)) := by
  let bad := smallWorkerTailEvent n (compromiseQ n) b stop ∪
    largeFirmScoreHeavyWorkerTail n (compromiseQ n) s b (stop - 1)
  have hsub : Imbalanced.compromiseLargeScore n s ≤ᵐ[profileMeasureWithWorkers n (n + 1)]
      profileUniformMarks ⁻¹' bad := by
    filter_upwards [ae_marksStable_profileUniformMarks_iff n (n + 1) (switchingCost n),
      ae_profileUniformMarks_matching_eq_exp_neg n (n + 1)] with p hp hm
    rintro ⟨m, hstable, hscore⟩
    have hstable' := (hp m).mpr hstable
    have hsum : s ≤ ∑ i, ((profileUniformMarks p i (m i)).1 : ℝ) := by
      simpa only [(hm m).1, Imbalanced.compromiseFirmScore] using hscore.le
    by_cases htail : workerTailMass b (fun i ↦ ((profileUniformMarks p i (m i)).2 : ℝ)) < stop - 1
    · exact Or.inl ⟨m, hstable', htail⟩
    · exact Or.inr ⟨m, hstable', hsum, le_of_not_gt htail⟩
  exact (measure_mono_ae hsub).trans
    (((measurePreserving_profileUniformMarks n (n + 1)).measure_preimage_le bad).trans
      (measure_union_le _ _))

/-- The remaining exceptional markets each contain at least one of the assignments
counted in the paper's first moment. -/
theorem measure_largeFirmScore_le_tail_add_expectedCount (n : ℕ) (s b stop : ℝ) :
    profileMeasureWithWorkers n (n + 1) (Imbalanced.compromiseLargeScore n s) ≤
      marksProfileMeasure n (n + 1) (smallWorkerTailEvent n (compromiseQ n) b stop) +
      expectedStableAssignmentCount n (compromiseQ n) s b (stop - 1) :=
  (measure_largeFirmScore_le_tail_add_heavy n s b stop).trans <| add_le_add le_rfl
    (measure_largeFirmScoreHeavyWorkerTail_le_expectedCount n _ _ _ _)

/-- Once the probability of any small-tail stable assignment vanishes, the finite
first-moment bound forces the probability of any large firm score to vanish. -/
theorem tendsto_largeFirmScore_of_workerTail
    (htail : Tendsto (fun n : ℕ ↦ marksProfileMeasure n (n + 1)
      (smallWorkerTailEvent n (compromiseQ n) (workerMarkCutoff n) (historyGrowthTarget n)))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (profileMeasureWithWorkers n (n + 1)).real
      (Imbalanced.compromiseLargeScore n (firmScoreCutoff n))) atTop (𝓝 0) := by
  apply (ENNReal.tendsto_toReal_zero_iff (fun _ ↦ measure_ne_top _ _)).mpr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using htail.add tendsto_expectedStableAssignmentCount_zero)
    (Eventually.of_forall fun _ ↦ zero_le)
    (Eventually.of_forall fun n ↦ measure_largeFirmScore_le_tail_add_expectedCount n _ _ _)

end WorkerCompromiseProof.Bounds.Paper
