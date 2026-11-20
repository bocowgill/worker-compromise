/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WorkerCompromiseProof.CapacityEstimate
public import WorkerCompromiseProof.Edge

/-!
# Joint payoffs attainable in a one-extra-worker market

The auxiliary worker score dominates cardinal utility and the log of the inverse rank
percentile. With high probability, every assignment has mean firm utility plus mean
worker score strictly below $(1+\eta)\log n$, for any fixed $\eta>0$.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open Filter MeasureTheory SwitchingCostMatching
open scoped BigOperators Topology

/-- Mean of the joint firm utility and worker score on the assigned edges. -/
noncomputable def jointMean {n w : ℕ} (p : Profile n w) (m : Matching n w) : ℝ :=
  (∑ i, (p (false, i, m i) + workerScore p i (m i))) / n

/-- A market admits some injection meeting the joint-score threshold. -/
def capacityFailure (n : ℕ) (η : ℝ) : Set (Profile n (n + 1)) :=
  {p | ∃ m : Matching n (n + 1), (1 + η) * Real.log n ≤ jointMean p m}

theorem measurableSet_capacityFailure (n : ℕ) (η : ℝ) :
    MeasurableSet (capacityFailure n η) := by
  apply Measurable.setOf
  refine Measurable.exists fun m ↦ ?_
  have h : Measurable (fun p ↦ jointMean (n := n) (w := n+1) p m) := by
    exact (Finset.measurable_sum _ fun i _ ↦
      (measurable_pi_apply (false, i, m i)).add (measurable_workerScore i (m i))).div_const _
  exact (measurableSet_le measurable_const h).mem

/-- Finite Markov bound over all assignments for the joint payoff. -/
theorem capacityFailure_measureReal_le {n : ℕ} (hn : 0 < n) (η : ℝ) {t : ℝ}
    (ht : 0 < t) (ht1 : t < 1) :
    (profileMeasureWithWorkers n (n + 1)).real (capacityFailure n η) ≤
      ((n : ℝ) + 1) * (2 / (1 - t) ^ 2) / (n : ℝ) ^ (t * (1 + η)) := by
  let a (i : Fin n) (j : Fin (n + 1)) (p : Profile n (n + 1)) :=
    p (false, i, j) + workerScore p i j
  have h := measureReal_exists_highMean_le (profileMeasureWithWorkers n (n + 1)) hn a
    (u := (1 + η) * Real.log n) ht.le (fun i j ↦ integrable_exp_edgeScore i j ht ht1)
    (fun i j ↦ integral_exp_edgeScore_le i j ht ht1)
  refine (measureReal_mono (s₂ := {p | ∃ m : Fin n → Fin (n + 1),
    (1 + η) * Real.log n ≤ (∑ i, a i (m i) p) / n}) ?_ (measure_ne_top _ _)).trans
    (h.trans_eq ?_)
  · rintro p ⟨m, hm⟩
    exact ⟨m, hm⟩
  · rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hn)]
    push_cast
    ring_nf

/-- In the ordinary market, the probability of any assignment violating the strict
joint payoff bound tends to zero. -/
theorem capacityFailure_tendsto_zero {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ ↦ (profileMeasureWithWorkers n (n + 1)).real (capacityFailure n η))
      atTop (𝓝 0) := by
  have hone : 0 < 1 + η := by linarith
  have hfrac : 1 / (1 + η) < 1 := (div_lt_iff₀ hone).2 (by linarith)
  obtain ⟨t, ht, ht1⟩ := exists_between hfrac
  have ht0 : 0 < t := lt_trans (by positivity : 0 < 1 / (1 + η)) ht
  have hgt : 1 < t * (1 + η) := (div_lt_iff₀ hone).1 ht
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_
    (tendsto_capacity_prefactor hgt (2 / (1 - t) ^ 2))
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact capacityFailure_measureReal_le (by omega) η ht0 ht1

end WorkerCompromiseProof.Bounds.Paper
