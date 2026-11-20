module

public import WorkerCompromiseProof.Tail
public import WorkerCompromiseProof.FirstMoment
public import WorkerCompromiseProof.Capacity
public import WorkerCompromiseProof.Welfare

/-!
# One extra worker rules out the square-root welfare compromise

The profile is drawn once from the ordinary exponential market. On a single market
event of probability tending to one, the two strict worker bounds hold for every
stable injection. The unmatched worker and the injection can depend on all preferences.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open Filter MeasureTheory SwitchingCostMatching Imbalanced
open scoped Topology

/-- The two welfare inequalities hold for every stable assignment in this realized market. -/
def allStableWorkerBounds (n : ℕ) (δ : ℝ) : Set (Profile n (n+1)) :=
  {p | ∀ m : Matching n (n+1), IsStable p (switchingCost n) m →
    (n : ℝ) ^ (1/2 + δ) < matchedWorkerAverageRank p m ∧
    matchedWorkerMeanUtility p m < (1/2 - δ) * Real.log n}

theorem allStableWorkerBounds_eq_compl (n : ℕ) (δ : ℝ) :
    allStableWorkerBounds n δ = (compromiseOrdinalFailure n δ ∪ compromiseCardinalFailure n δ)ᶜ := by
  classical
  ext p
  constructor
  · intro h
    rintro (⟨m, hm, hbad⟩ | ⟨m, hm, hbad⟩)
    · exact ((h m hm).1.not_ge hbad)
    · exact ((h m hm).2.not_ge hbad)
  · intro h m hm
    exact ⟨lt_of_not_ge (fun hr ↦ h (Or.inl ⟨m, hm, hr⟩)),
      lt_of_not_ge (fun hu ↦ h (Or.inr ⟨m, hm, hu⟩))⟩

/-- One of two market-wide restrictions must fail if any stable assignment violates
either worker bound. The two restrictions do not need to be independent. -/
theorem workerFailure_subset {n : ℕ} (hn : 0 < n) :
    compromiseOrdinalFailure n (1/400000) ∪ compromiseCardinalFailure n (1/400000) ⊆
      compromiseLargeScore n (firmScoreCutoff n) ∪ capacityFailure n (1/400000) := by
  intro p hp
  by_contra hout
  have hgood : p ∈ allStableWorkerBounds n (1/400000) := by
    intro m hstable
    apply welfare_of_cutoffs hn
    · have hS : compromiseFirmScore p m ≤ firmScoreCutoff n := le_of_not_gt fun h ↦
        hout (Or.inl ⟨m, hstable, h⟩)
      simpa only [firmScoreCutoff, show (2 : ℝ) * (1 / 400000) = 1 / 200000 by norm_num] using hS
    · exact lt_of_not_ge (fun h ↦ hout (Or.inr ⟨m, h⟩))
  rw [allStableWorkerBounds_eq_compl] at hgood
  exact hgood hp

/-- The probability of a stable witness to either violation tends to zero. -/
theorem workerFailure_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (profileMeasureWithWorkers n (n+1)).real
      (compromiseOrdinalFailure n (1/400000) ∪ compromiseCardinalFailure n (1/400000)))
      atTop (𝓝 0) := by
  have ht := smallWorkerTail_tendsto_zero compromiseQ
    (eventually_compromiseQ_ge_half.mono fun n h ↦ ⟨h, compromiseQ_le_one n⟩)
  have hs := tendsto_largeFirmScore_of_workerTail ht
  have hc := capacityFailure_tendsto_zero (η := 1/400000) (by norm_num)
  refine squeeze_zero' (.of_forall fun _ ↦ measureReal_nonneg) ?_ (by simpa only [add_zero] using hs.add hc)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (measureReal_mono (workerFailure_subset hn) (measure_ne_top _ _)).trans
    (measureReal_union_le _ _)

/-- Theorem 1 of the paper, with both strict bounds on the same market event. -/
theorem allStableWorkerBounds_tendsto_one :
    Tendsto (fun n : ℕ ↦ (profileMeasureWithWorkers n (n+1)).real
      (allStableWorkerBounds n (1/400000))) atTop (𝓝 1) := by
  have h := tendsto_const_nhds (x := (1 : ℝ)) |>.sub workerFailure_tendsto_zero
  simpa only [allStableWorkerBounds_eq_compl, probReal_compl_eq_one_sub
    ((measurableSet_compromiseOrdinalFailure _ _).union (measurableSet_compromiseCardinalFailure _ _)),
    sub_zero] using h

/-- The best ordinal and cardinal compromises both miss their respective half benchmarks
in the same realized market, even if they use different maximizing or minimizing assignments. -/
theorem optimalCompromises_tendsto_one :
    Tendsto (fun n : ℕ ↦ (profileMeasureWithWorkers n (n+1)).real
      {p | 1/2 + 1/400000 < ordinalCompromiseExponent p (switchingCost n) ∧
        bestUtilityCompromise p (switchingCost n) < 1/2 - 1/400000})
      atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' allStableWorkerBounds_tendsto_one
    tendsto_const_nhds ?_ (.of_forall fun _ ↦ measureReal_le_one)
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  apply measureReal_mono _ (measure_ne_top _ _)
  intro p hp
  rw [allStableWorkerBounds_eq_compl] at hp
  exact ⟨ordinalCompromiseExponent_gt_of_not_mem_compromiseOrdinalFailure hn
    (fun h ↦ hp (Or.inl h)), bestUtilityCompromise_lt_of_not_mem_compromiseCardinalFailure hn
      (by norm_num) (fun h ↦ hp (Or.inr h))⟩

end WorkerCompromiseProof.Bounds.Paper
