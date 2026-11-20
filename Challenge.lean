/-
The market definitions adapt work by the Formal Conjectures Authors (2026) and
the Market First Bridge Contributors (2026), licensed under Apache 2.0.
-/
module

public import Mathlib

/-!
# Worker welfare with one extra worker

There are `n` firms and `n + 1` workers. The directed utilities for each pair are
independent rate-one exponentials. A matching assigns each firm a distinct worker.
The probability below draws the utility profile once. The bounds then hold for
every stable assignment in that market, including assignments selected after
observing all utilities. Codex helped formalize the result in Lean.
-/

@[expose] public section

namespace WorkerCompromise

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology

/-- A utility profile specifies two directed utilities for each firm–worker pair. -/
abbrev Profile (n w : ℕ) := (Bool × Fin n × Fin w) → ℝ

/-- An assignment sends each firm to a distinct worker. -/
abbrev Matching (n w : ℕ) := Fin n ↪ Fin w

/-- The Boolean index is `false` for firm utility and `true` for worker utility. -/
noncomputable def marketMeasure (n : ℕ) : Measure (Profile n (n + 1)) :=
  Measure.pi fun _ ↦ expMeasure 1

/-- The gain threshold for switching partners when the market has `n` firms. -/
noncomputable def switchingCost (n : ℕ) : ℝ :=
  Real.log n / (6 * Real.sqrt n)

/-- A firm and a worker can block when the firm gains strictly more than the cost.
A matched worker must also gain strictly more than the cost. An unmatched worker
is willing to accept any offer. -/
def IsBlockingPair {n w : ℕ} (p : Profile n w) (ε : ℝ) (m : Matching n w)
    (i : Fin n) (j : Fin w) : Prop :=
  j ≠ m i ∧ p (false, i, m i) + ε < p (false, i, j) ∧
    ∀ k, m k = j → p (true, k, j) + ε < p (true, i, j)

/-- An assignment is stable when every firm–worker pair fails the blocking test. -/
def IsStable {n w : ℕ} (p : Profile n w) (ε : ℝ) (m : Matching n w) : Prop :=
  ∀ i j, ¬ IsBlockingPair p ε m i j

/-- Partner ranks count all alternatives at least as good as the assigned partner.
The assigned partner counts, so the best rank is one almost surely. -/
noncomputable def matchedWorkerAverageRank {n w : ℕ} (p : Profile n w) (m : Matching n w) : ℝ :=
  ((∑ i : Fin n, ∑ k : Fin n, if p (true, i, m i) ≤ p (true, k, m i) then 1 else 0 : ℕ) : ℝ) / n

/-- Mean assigned utility of the `n` matched workers. -/
noncomputable def matchedWorkerMeanUtility {n w : ℕ} (p : Profile n w) (m : Matching n w) : ℝ :=
  (∑ i : Fin n, p (true, i, m i)) / n

/-- Both welfare bounds hold for the same market, for every stable assignment. -/
def allStableWorkerBounds (n : ℕ) (δ : ℝ) : Set (Profile n (n + 1)) :=
  {p | ∀ m : Matching n (n + 1), IsStable p (switchingCost n) m →
    (n : ℝ) ^ (1 / 2 + δ) < matchedWorkerAverageRank p m ∧
      matchedWorkerMeanUtility p m < (1 / 2 - δ) * Real.log n}

/-- With probability tending to one, every stable assignment satisfies both strict bounds. -/
theorem allStableWorkerBounds_tendsto_one :
    Tendsto (fun n : ℕ ↦ (marketMeasure n).real (allStableWorkerBounds n (1 / 400000)))
      atTop (𝓝 1) := by
  sorry

/-- The finite set of all assignments that are stable at switching cost `ε`. -/
noncomputable def stableMatchings {n w : ℕ} (p : Profile n w) (ε : ℝ) : Finset (Matching n w) :=
  Finset.univ.filter fun m ↦ IsStable p ε m

/-- Mean assigned-partner rank across firms, each of which ranks all `w` workers. -/
noncomputable def firmAverageRank {n w : ℕ} (p : Profile n w) (m : Matching n w) : ℝ :=
  ((∑ i : Fin n, ∑ j : Fin w, if p (false, i, m i) ≤ p (false, i, j) then 1 else 0 : ℕ) : ℝ) / n

/-- The ordinal compromise takes the worse (larger) of the two sides' average ranks. -/
noncomputable def rankCompromise {n w : ℕ} (p : Profile n w) (m : Matching n w) : ℝ :=
  max (firmAverageRank p m) (matchedWorkerAverageRank p m)

/-- An unmatched worker has utility zero. -/
noncomputable def workerRealizedUtility {n w : ℕ} (p : Profile n w) (m : Matching n w)
    (j : Fin w) : ℝ :=
  ∑ i : Fin n, if m i = j then p (true, i, j) else 0

/-- The cardinal compromise takes the smaller normalized mean utility of the two populations.
The worker mean divides by the number of workers, including the unmatched worker. -/
noncomputable def utilityCompromise {n w : ℕ} (p : Profile n w) (m : Matching n w) : ℝ :=
  min (((∑ i : Fin n, p (false, i, m i)) / n) / Real.log n)
    (((∑ j : Fin w, workerRealizedUtility p m j) / w) / Real.log n)

/-- Minimize the rank compromise over stable assignments and take its log base `n`. -/
noncomputable def ordinalCompromiseExponent {n w : ℕ} (p : Profile n w) (ε : ℝ) : ℝ :=
  let S := stableMatchings p ε
  Real.log (if hs : S.Nonempty then (S.image (rankCompromise p)).min' (hs.image _) else 1) /
    Real.log n

/-- Maximize the utility compromise over stable assignments. The stable set is nonempty in
the markets considered in the theorem. -/
noncomputable def bestUtilityCompromise {n w : ℕ} (p : Profile n w) (ε : ℝ) : ℝ :=
  let S := stableMatchings p ε
  if hs : S.Nonempty then (S.image (utilityCompromise p)).max' (hs.image _) else 0

/-- Both optimal compromises miss their half benchmarks on the same market event. The
ordinal and cardinal objectives can select different stable assignments. -/
theorem optimalCompromises_tendsto_one :
    Tendsto (fun n : ℕ ↦ (marketMeasure n).real
      {p | 1 / 2 + 1 / 400000 < ordinalCompromiseExponent p (switchingCost n) ∧
        bestUtilityCompromise p (switchingCost n) < 1 / 2 - 1 / 400000}) atTop (𝓝 1) := by
  sorry

end WorkerCompromise
