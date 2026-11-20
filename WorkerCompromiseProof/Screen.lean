/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WorkerCompromiseProof.Core.RowEvents

/-!
# The screen at a fixed partial assignment

Under the product law of the unused rows, the number of forced firms has
a binomial lower tail. Keeping the threshold real avoids losing a row
when the required batch size is not an integer.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

/-- A lower-tail bound at a real threshold below half the mean count. -/
private theorem measure_count_lt_half {ι A : Type*} [Fintype ι] [MeasurableSpace A]
    (ρ : Measure A) [IsProbabilityMeasure ρ] (G : Set A) (I : Finset ι) (k : ℝ)
    (hG : MeasurableSet G) (hk : k ≤ (I.card : ℝ) * ρ.real G / 2) :
    (Measure.pi (fun _ : ι ↦ ρ)) {x | ((I.filter (fun i ↦ x i ∈ G)).card : ℝ) < k} ≤
      ENNReal.ofReal (Real.exp (-((I.card : ℝ) * ρ.real G) / 8)) := by
  let μ := Measure.pi (fun _ : ι ↦ ρ)
  let X : (ι → A) → ℝ := fun x ↦ (I.filter (fun i ↦ x i ∈ G)).card
  let f : ι → A → ℝ := fun i a ↦
    if i ∈ I then G.piecewise (fun _ ↦ Real.exp (-1)) (fun _ ↦ 1) a else 1
  let p := ρ.real G
  let a := 1 - Real.exp (-1)
  have hf (x : ι → A) : Real.exp (-1 * X x) = ∏ i, f i (x i) := by
    rw [neg_one_mul]
    have hsum : X x = ∑ i ∈ I, if x i ∈ G then (1 : ℝ) else 0 := by
      simp only [X, Finset.sum_boole]
    rw [hsum, ← Finset.sum_neg_distrib, Real.exp_sum]
    calc
      _ = ∏ i ∈ I, f i (x i) := by
        refine Finset.prod_congr rfl fun i hi ↦ ?_
        by_cases hxi : x i ∈ G <;> simp [f, hi, Set.piecewise, hxi]
      _ = ∏ i, f i (x i) := Finset.prod_subset (Finset.subset_univ _) (by
        intro i _ hi
        simp [f, hi])
  have hint (i : ι) : Integrable (f i) ρ := by
    by_cases hi : i ∈ I
    · simpa [f, hi] using Integrable.piecewise (μ := ρ) hG.nullMeasurableSet
        (integrable_const (Real.exp (-1))).integrableOn (integrable_const (1 : ℝ)).integrableOn
    · simp [f, hi]
  have hcoord (i : ι) : (∫ z, f i z ∂ρ) = if i ∈ I then 1 - a * p else 1 := by
    by_cases hi : i ∈ I
    · simp only [f, hi, ite_true]
      rw [integral_piecewise hG (integrable_const _).integrableOn
        (integrable_const _).integrableOn]
      rw [integral_const, integral_const, smul_eq_mul, smul_eq_mul,
        measureReal_restrict_apply_univ, measureReal_restrict_apply_univ, measureReal_compl hG]
      rw [probReal_univ]
      dsimp [a, p]
      ring
    · simp [f, hi]
  have hm : mgf X μ (-1) = (1 - a * p) ^ I.card := by
    simp only [mgf, hf, μ, integral_fintype_prod_eq_prod, hcoord, ← Finset.prod_filter,
      Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const]
  have hp : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := by
    rw [show (1 : ℝ) = ρ.real Set.univ from probReal_univ.symm]
    exact measureReal_mono (Set.subset_univ G)
  have ha : 5 / 8 ≤ a := by dsimp [a]; linarith [Real.exp_neg_one_lt_d9]
  have hnonneg : 0 ≤ 1 - a * p := by
    have := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ a by linarith)
    dsimp [a] at *
    linarith [Real.exp_pos (-1)]
  have hpow : (1 - a * p) ^ I.card ≤ Real.exp (-(I.card : ℝ) * (a * p)) := by
    rw [neg_mul, ← mul_neg, Real.exp_nat_mul]
    exact pow_le_pow_left₀ hnonneg (Real.one_sub_le_exp_neg _) _
  have hch := measure_le_le_exp_mul_mgf (X := X) (μ := μ) (t := -1) k (by norm_num)
    (by simp only [hf, μ]; exact Integrable.fintype_prod hint)
  have hbound : μ.real {x | X x < k} ≤ Real.exp (-((I.card : ℝ) * p) / 8) := calc
    μ.real {x | X x < k} ≤ μ.real {x | X x ≤ k} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro x hx
      exact (show X x < k from hx).le
    _ ≤ Real.exp k * (1 - a * p) ^ I.card := by simpa [hm] using hch
    _ ≤ Real.exp (-((I.card : ℝ) * p) / 8) := by
      apply (mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)).trans
      rw [← Real.exp_add, Real.exp_le_exp]
      have hma := mul_le_mul_of_nonneg_right ha (show 0 ≤ (I.card : ℝ) * p by positivity)
      nlinarith only [hk, hma]
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _), μ, X, p]
    using ENNReal.ofReal_le_ofReal hbound

/-- At a fixed partial assignment, too few forced rows occur with probability at most
$\exp(-D/(512b))$, including the case of a noninteger threshold. -/
theorem measure_forcedRows_few_le {n : ℕ} (I : Finset (Fin n))
    (u : Fin (n + 1)) (J : Finset (Fin (n + 1))) (v : Fin (n + 1) → ℝ) (q b D : ℝ)
    (hn : 2 ≤ n) (hu : u ∉ J) (hq : q ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hb : 0 < b) (hb₁ : b ≤ 1) (hnb : 1 ≤ (n : ℝ) * b)
    (hv : ∀ j ∈ J, v j ∈ Set.Icc (0 : ℝ) 1) (hD : D = 1 + ∑ j ∈ J, v j)
    (hsmall : D ≤ (n : ℝ) * b) (hcard : (n : ℝ) / 2 ≤ (I.card : ℝ)) :
    marksProfileMeasure n (n + 1) {x | ((I.filter (fun i ↦
      x i ∈ forcedRowsEvent u J v q (1 / ((n : ℝ) * b)) b)).card : ℝ) < D / (128 * b)} ≤
        ENNReal.ofReal (Real.exp (-D / (512 * b))) := by
  let t := 1 / ((n : ℝ) * b)
  let G := forcedRowsEvent u J v q t b
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnb' : (0 : ℝ) < (n : ℝ) * b := mul_pos hn' hb
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by dsimp [t]; positivity, (div_le_one hnb').2 hnb⟩
  have htb : t * b = 1 / (n : ℝ) := by
    dsimp [t]
    field_simp
  have hsmall' : t * (1 + ∑ j ∈ J, v j) ≤ 1 := by
    rw [← hD]
    dsimp [t]
    rw [one_div_mul_eq_div]
    exact (div_le_one hnb').2 hsmall
  have hp : D / (32 * ((n : ℝ) * b)) ≤ (marksRowMeasure (n + 1)).real G := by
    have hp' := measureReal_forcedRowsEvent_lower hn hu hq ht ⟨hb.le, hb₁⟩ htb hv hsmall'
    rw [← hD] at hp'
    convert hp' using 1
    dsimp [t]
    ring
  have hD₀ : 0 ≤ D := by
    rw [hD]
    linarith [Finset.sum_nonneg (fun j hj ↦ (hv j hj).1)]
  have hmean : D / (64 * b) ≤ (I.card : ℝ) * (marksRowMeasure (n + 1)).real G := by
    calc
      D / (64 * b) = (n : ℝ) / 2 * (D / (32 * ((n : ℝ) * b))) := by
        field_simp
        ring
      _ ≤ _ := mul_le_mul hcard hp (by positivity) (by positivity)
  have hk : D / (128 * b) ≤ (I.card : ℝ) * (marksRowMeasure (n + 1)).real G / 2 := by
    linarith only [hmean, show D / (128 * b) = (D / (64 * b)) / 2 by ring]
  refine (measure_count_lt_half (marksRowMeasure (n + 1)) G I _
    (measurableSet_forcedRowsEvent u J v q t b) hk).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  rw [show -D / (512 * b) = -(D / (64 * b)) / 8 by ring]
  linarith only [hmean]

end WorkerCompromiseProof.Bounds.Paper
