module

public import WorkerCompromiseProof.Core.CascadeLimit
public import WorkerCompromiseProof.Scales
public import WorkerCompromiseProof.Cascade

/-!
# Uniform exclusion of a small worker tail

Specialize the backward induction at the empty partial assignment to the paper's
scale schedule. The probability counts markets in which *some* stable injection
violates the bound, with the unmatched worker also chosen from the realized market.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open Filter MeasureTheory
open scoped ENNReal Topology

/-- The paper's explicit exceptional probability, uniform over every stable assignment. -/
theorem eventually_measure_smallWorkerTail_le :
    ∀ᶠ n : ℕ in atTop, ∀ q ∈ Set.Icc (1/2 : ℝ) 1,
      marksProfileMeasure n (n+1)
        (smallWorkerTailEvent n q (workerMarkCutoff n) (historyGrowthTarget n)) ≤
        ENNReal.ofReal (((n : ℝ) + 1) * Real.exp (-((Real.log n)^2) / 1024)) := by
  filter_upwards [eventually_stageScale_hypotheses, eventually_stageCount_growth,
    eventually_inverse_stageScale] with n hs hg hinv q hq
  obtain ⟨hn, hs⟩ := hs
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hg' : historyGrowthTarget n ≤ (129/128 : ℝ) ^ stageCount n :=
    hg.trans (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
  have hbound := Paper.measure_exists_stable_smallWorkerTail_le (stageScale n) hn hq hg'
    (fun l hl ↦ (hs l hl).1) (fun l _ ↦ stageScale_succ n l)
    (fun l hl ↦ (hs l hl).2.2.2.1)
    (fun l hl ↦ ⟨(hs l hl.le).2.1, (hs l hl.le).2.2.1, (hs l hl.le).2.2.2.2.1, hinv l⟩)
  refine hbound.trans_eq ?_
  rw [stageScale_zero, show (-1 : ℝ) / (1024 * ((Real.log n)^2)⁻¹) =
    -((Real.log n)^2) / 1024 by field_simp [hlog.ne']]
  rw [ENNReal.ofReal_mul (by positivity)]
  norm_cast

/-- Market probability of at least one stable small-tail assignment tends to zero. -/
theorem smallWorkerTail_tendsto_zero (q : ℕ → ℝ)
    (hq : ∀ᶠ n : ℕ in atTop, q n ∈ Set.Icc (1/2 : ℝ) 1) :
    Tendsto (fun n : ℕ ↦ marksProfileMeasure n (n+1)
      (smallWorkerTailEvent n (q n) (workerMarkCutoff n) (historyGrowthTarget n)))
      atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal tendsto_vacancy_error)
    (.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hq, eventually_measure_smallWorkerTail_le] with n hqn hn
  exact hn _ hqn

end WorkerCompromiseProof.Bounds.Paper
