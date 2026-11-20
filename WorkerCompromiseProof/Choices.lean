/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WorkerCompromiseProof.Core.RowEvents

/-!
# Summing over all named partners

Skipping a row has weight one. Naming a partner incurs a measurable cost in that row.
The product law and finite distributivity pay for all choices, including repeated partners.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Independently drawn rows factor the total weight of the possible labeled extensions. -/
theorem sum_integral_choices_le {n : ℕ}
    (weight : Fin n → Fin n → MarksRow (n+1) → ℝ≥0∞) (c : ℝ≥0∞)
    (hmeas : ∀ i j, Measurable (weight i j))
    (havg : ∀ i j, (∫⁻ r, weight i j r ∂marksRowMeasure (n+1)) ≤ c) :
    (∑ F : Fin n → Option (Fin n), ∫⁻ x, ∏ i, (F i).elim 1 (fun j ↦ weight i j (x i))
      ∂marksProfileMeasure n (n+1)) ≤ (1 + n*c)^n := by
  classical
  let μ := marksRowMeasure (n+1)
  let w (i : Fin n) (j : Option (Fin n)) (r : MarksRow (n+1)) : ℝ≥0∞ :=
    j.elim 1 (fun a ↦ weight i a r)
  have hm (i : Fin n) (j : Option (Fin n)) : Measurable (w i j) := by
    cases j with
    | none => exact measurable_const
    | some j => exact hmeas i j
  have hfactor (F : Fin n → Option (Fin n)) :
      (∫⁻ x, ∏ i, w i (F i) (x i) ∂marksProfileMeasure n (n+1)) =
      ∏ i, ∫⁻ r, w i (F i) r ∂μ := by
    have hi := iIndepFun_pi (μ := fun _ : Fin n ↦ μ)
      (X := fun i ↦ w i (F i)) (fun i ↦ (hm i (F i)).aemeasurable)
    change (∫⁻ x, ∏ i, w i (F i) (x i) ∂Measure.pi (fun _ : Fin n ↦ μ)) = _
    rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
      (fun i (x : MarksProfile n (n+1)) ↦ w i (F i) (x i)) hi (fun i ↦ (hm i (F i)).comp (measurable_pi_apply i))]
    exact Finset.prod_congr rfl fun i _ ↦
      (measurePreserving_eval (fun _ : Fin n ↦ μ) i).lintegral_comp (hm i (F i))
  change (∑ F : Fin n → Option (Fin n), ∫⁻ x, ∏ i, w i (F i) (x i)
    ∂marksProfileMeasure n (n+1)) ≤ _
  simp_rw [hfactor]
  rw [← Fintype.prod_sum (fun (i : Fin n) (j : Option (Fin n)) ↦ ∫⁻ r, w i j r ∂μ)]
  calc
    _ ≤ ∏ _ : Fin n, (1 + n*c) := by
      apply Finset.prod_le_prod
      intro i _
      rw [Fintype.sum_option]
      have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ havg i j)
      simpa [w, μ, nsmul_eq_mul] using add_le_add_left hsum 1
    _ = _ := by simp

/-- The next scale pays for all labeled branches as well as the lower-tail failure. -/
theorem paper_step_weight_le {n : ℕ} {D b : ℝ} (hn : 0 < n) (hb : 0 < b)
    (hd : 1024 ≤ D/b) :
    Real.exp (-8*D/b) * (1 + (n : ℝ)*(1/((n:ℝ)*b))^2*D*b/8)^n +
        Real.exp (-D/(512*b)) ≤ Real.exp (-D/(1024*b)) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let a := (n : ℝ)*(1/((n:ℝ)*b))^2*D*b/8
  have hD : 0 ≤ D := by
    have h := (le_div_iff₀ hb).mp hd
    linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hexp : (1+a)^n ≤ Real.exp ((n : ℝ)*a) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp a]) _
  have heq : (n : ℝ)*a = D/(8*b) := by
    dsimp [a]
    field_simp
  have hterm : Real.exp (-8*D/b) * (1+a)^n ≤ Real.exp (-D/(512*b)) := by
    refine (mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le).trans ?_
    rw [heq, ← Real.exp_add, Real.exp_le_exp]
    field_simp
    linarith
  have hsmall : 2 ≤ Real.exp (D/(1024*b)) := Real.exp_one_gt_two.le.trans
    (Real.exp_le_exp.mpr (by field_simp at hd ⊢; linarith))
  calc
    _ ≤ 2*Real.exp (-D/(512*b)) := by linarith only [hterm]
    _ ≤ Real.exp (D/(1024*b)) * Real.exp (-D/(512*b)) :=
      mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The induction step on the extended nonnegative reals, with the failure term first. -/
theorem paper_step_weight_ennreal_le {n : ℕ} {D b : ℝ} (hn : 0 < n) (hb : 0 < b)
    (hd : 1024 ≤ D/b) :
    ENNReal.ofReal (Real.exp (-D/(512*b))) +
      ENNReal.ofReal (Real.exp (-8*D/b)) *
        (1 + (n : ℝ≥0∞)*ENNReal.ofReal ((1/((n:ℝ)*b))^2*D*b/8))^n ≤
      ENNReal.ofReal (Real.exp (-D/(1024*b))) := by
  have hd' := (le_div_iff₀ hb).mp hd
  have hD : 0 ≤ D := by linarith
  have hc : 0 ≤ (1 / ((n : ℝ)*b))^2*D*b/8 := by positivity
  have h := ENNReal.ofReal_le_ofReal (paper_step_weight_le hn hb hd)
  rw [add_comm]
  simp only [show (n : ℝ)*(1/((n:ℝ)*b))^2*D*b/8 =
    (n:ℝ)*((1/((n:ℝ)*b))^2*D*b/8) by ring] at h
  simpa (disch := positivity) only [ENNReal.ofReal_add, ENNReal.ofReal_mul, ENNReal.ofReal_pow,
    ENNReal.ofReal_one, ENNReal.ofReal_natCast] using h

end WorkerCompromiseProof.Bounds.Paper
