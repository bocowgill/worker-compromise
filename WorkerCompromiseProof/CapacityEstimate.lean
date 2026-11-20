/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic

/-!
# A bound on scores attainable by selecting edges

Jensen's inequality turns any high-scoring selection of partners into a large sum
over the entire market. Markov's inequality then needs only a moment bound for
one edge at a time, even when different edge scores are dependent.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open Filter MeasureTheory
open scoped BigOperators Topology

/-- Jensen's inequality for the arithmetic mean of a nonempty vector. -/
theorem exp_mean_le_mean_exp {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    Real.exp ((∑ i, a i) / n) ≤ (∑ i, Real.exp (a i)) / n := by
  have h := convexOn_exp.map_centerMass_le (t := Finset.univ) (w := fun _ : Fin n ↦ (1 : ℝ))
    (p := a) (by simp) (by simpa using (Nat.cast_pos.mpr hn : 0 < (n : ℝ)))
    (fun _ _ ↦ Set.mem_univ _)
  simpa [Finset.centerMass, smul_eq_mul, div_eq_inv_mul] using h

/-- Even a market-dependent partner choice is bounded by the sum over all edges. -/
theorem exp_assignmentMean_le_allEdges {n w : ℕ} (hn : 0 < n)
    (a : Fin n → Fin w → ℝ) (m : Fin n → Fin w) (t : ℝ) :
    Real.exp (t * ((∑ i, a i (m i)) / n)) ≤
      (∑ i, ∑ j, Real.exp (t * a i j)) / n := by
  rw [← mul_div_assoc, Finset.mul_sum]
  refine (exp_mean_le_mean_exp hn _).trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n))
  exact Finset.sum_le_sum fun i _ ↦ Finset.single_le_sum
    (f := fun j ↦ Real.exp (t * a i j)) (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ (m i))

/-- A one-edge exponential moment bounds the probability that *any* partner selection
attains the prescribed mean score. The selection may even choose the same partner twice. -/
theorem measureReal_exists_highMean_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {n w : ℕ} (hn : 0 < n)
    (a : Fin n → Fin w → Ω → ℝ) {t K u : ℝ} (ht : 0 ≤ t)
    (hint : ∀ i j, Integrable (fun p ↦ Real.exp (t * a i j p)) μ)
    (hbound : ∀ i j, (∫ p, Real.exp (t * a i j p) ∂μ) ≤ K) :
    μ.real {p | ∃ m : Fin n → Fin w, u ≤ (∑ i, a i (m i) p) / n} ≤
      w * K / Real.exp (t * u) := by
  let Z (p : Ω) : ℝ := (∑ i, ∑ j, Real.exp (t * a i j p)) / n
  have hZ : Integrable Z μ :=
    (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j).div_const n
  have hsub : {p | ∃ m : Fin n → Fin w, u ≤ (∑ i, a i (m i) p) / n} ⊆
      {p | Real.exp (t * u) ≤ Z p} := by
    rintro p ⟨m, hm⟩
    exact ((Real.exp_le_exp).mpr (mul_le_mul_of_nonneg_left hm ht)).trans
      (exp_assignmentMean_le_allEdges hn (fun i j ↦ a i j p) m t)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := Z)
    (ae_of_all _ fun p ↦ by dsimp [Z]; positivity) hZ (Real.exp (t * u))
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ((le_div_iff₀ (Real.exp_pos _)).2 ?_)
  rw [mul_comm]
  refine hmarkov.trans ?_
  unfold Z
  rw [integral_div, integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j)]
  simp_rw [integral_finsetSum _ (fun j _ ↦ hint _ j)]
  refine (div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hbound i j)
    (Nat.cast_nonneg n)).trans_eq ?_
  simp [nsmul_eq_mul, mul_div_cancel_left₀, Nat.ne_of_gt hn]

/-- For exponent above one, the linear number of partners is absorbed by the power. -/
theorem tendsto_capacity_prefactor {a : ℝ} (ha : 1 < a) (K : ℝ) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) * K / (n : ℝ) ^ a) atTop (𝓝 0) := by
  have h₁ := (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp tendsto_natCast_atTop_atTop
  have h₂ := (tendsto_rpow_neg_atTop (zero_lt_one.trans ha)).comp tendsto_natCast_atTop_atTop
  refine (show Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ (-(a-1)) + (n : ℝ) ^ (-a)) * K)
      atTop (𝓝 0) by simpa using (h₁.add h₂).mul_const K).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [show -(a - 1) = 1 - a by ring, Real.rpow_sub hn', Real.rpow_one,
    Real.rpow_neg hn'.le]
  ring

end WorkerCompromiseProof.Bounds.Paper
