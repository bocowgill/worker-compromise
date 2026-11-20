module

public import WorkerCompromiseProof.Core.Welfare

/-!
# Worker scores for the joint payoff bound

On each edge the auxiliary score dominates both the worker's utility and the log of
the inverse rank percentile. Ranks include the evaluated firm itself.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory SwitchingCostMatching

/-- The inclusive rank of firm `i` on worker `j`'s list. -/
noncomputable def edgeRank {n w : ℕ} (p : Profile n w) (i : Fin n) (j : Fin w) : ℕ :=
  Imbalanced.inclusiveColumnRank i (fun k ↦ p (true, k, j))

/-- A worker's edge score bounding utility and the logarithm of inverse rank percentile. -/
noncomputable def workerScore {n w : ℕ} (p : Profile n w) (i : Fin n) (j : Fin w) : ℝ :=
  max (p (true, i, j)) (Real.log ((n : ℝ) / edgeRank p i j))

theorem measurable_edgeRank {n w : ℕ} (i : Fin n) (j : Fin w) :
    Measurable (fun p : Profile n w ↦ edgeRank p i j) :=
  (Imbalanced.measurable_inclusiveColumnRank i).comp
    (Measurable.of_eval (fun _ ↦ measurable_pi_apply _))

theorem measurable_workerScore {n w : ℕ} (i : Fin n) (j : Fin w) :
    Measurable (fun p : Profile n w ↦ workerScore p i j) := by
  exact (measurable_pi_apply _).max ((Measurable.of_discrete
    (f := fun r : ℕ ↦ Real.log ((n : ℝ) / r))).comp (measurable_edgeRank i j))

end WorkerCompromiseProof.Bounds.Paper
