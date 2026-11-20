/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Basic

/-!
# Finite covers by valid partial assignments

Candidate extensions that are incompatible with a partial assignment never enter the
probability bound. After bounding each valid term, its nonnegative weight can be summed
over the larger, unrestricted label space.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory Set
open scoped ENNReal

/-- Bound the probability of a market-level event by the failed screen and a sum over all
labels, using extension estimates only for labels satisfying the validity condition. -/
theorem measure_guarded_cover_le {α Ω : Type*} [Fintype α] [MeasurableSpace Ω]
    (μ : Measure Ω) (E S : Set Ω) (v : α → Prop) (A : ∀ f, v f → Set Ω) (w : α → ℝ≥0∞)
    (hc : ∀ x ∈ E, x ∈ S ∨ ∃ f h, x ∈ A f h)
    (hA : ∀ f h, μ (A f h) ≤ w f) : μ E ≤ μ S + ∑ f, w f := by
  classical
  let C (f : α) : Set Ω := if h : v f then A f h else ∅
  have hcover : E ⊆ S ∪ ⋃ f, C f := by
    intro x hx
    obtain hs | ⟨f, h, hx'⟩ := hc x hx
    · exact Or.inl hs
    · exact Or.inr (mem_iUnion.mpr ⟨f, by simpa [C, h] using hx'⟩)
  have hbound (f : α) : μ (C f) ≤ w f := by
    by_cases h : v f
    · simpa [C, h] using hA f h
    · simp [C, h]
  exact (measure_mono hcover).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl ((measure_iUnion_fintype_le μ C).trans (Finset.sum_le_sum fun f _ ↦
      hbound f))))

end WorkerCompromiseProof.Bounds.Paper
