/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib

/-!
# Matchings with switching costs

Adapted from the Formal Conjectures shared model. This version imports Mathlib
and retains the market definitions and probability instance used in the welfare proof.

The market model from Pittel and Rudov's
[Stable matchings under relaxed random preferences](https://doi.org/10.1007/s00182-026-01016-x).
The worker count defaults to one more than the firm count.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SwitchingCostMatching

/-- The two utilities for each firm-worker pair. `false` indexes the firm and `true` the worker. -/
abbrev Profile (n : ℕ) (w : ℕ := n + 1) := (Bool × Fin n × Fin w) → ℝ

/-- A matching assigns every firm a distinct worker. -/
abbrev Matching (n : ℕ) (w : ℕ := n + 1) := Fin n ↪ Fin w

/-- A pair blocks if the firm gains more than the switching cost and the worker either has no
partner or gains more than the switching cost. -/
def IsBlockingPair {n w : ℕ} (p : Profile n w) (ε : ℝ) (m : Matching n w) (i : Fin n)
    (j : Fin w) : Prop :=
  j ≠ m i ∧ p (false, i, m i) + ε < p (false, i, j) ∧
    ∀ k, m k = j → p (true, k, j) + ε < p (true, i, j)

/-- A matching is stable at cost $\varepsilon$ if no pair blocks at that cost. -/
def IsStable {n w : ℕ} (p : Profile n w) (ε : ℝ) (m : Matching n w) : Prop :=
  ∀ i j, ¬ IsBlockingPair p ε m i j

/-- The law of independent rate-one exponential utilities. -/
noncomputable def profileMeasureWithWorkers (n w : ℕ) : Measure (Profile n w) :=
  Measure.pi fun _ ↦ expMeasure 1

instance (n w : ℕ) : IsProbabilityMeasure (profileMeasureWithWorkers n w) := by
  let := isProbabilityMeasure_expMeasure (r := 1) zero_lt_one
  unfold profileMeasureWithWorkers
  infer_instance

end SwitchingCostMatching
