/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WorkerCompromiseProof.Core.RowEvents

/-!
# Expected weight of a specified fresh partner

The old blocking test and the proposed partner's marks are in disjoint columns.
The worker's actual mark enters the exponential weight.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

/-- Weight of retaining one specified partner, including the test on the old columns. -/
noncomputable def rowWeight {w : ℕ} (u : Fin w) (J : Finset (Fin w)) (v : Fin w → ℝ)
    (q t b : ℝ) (j : Fin w) (r : MarksRow w) : ℝ≥0∞ :=
  if r ∈ tight u J v q t ∧ (r j).1.val ≤ t ∧ b < (r j).2.val then
    ENNReal.ofReal (Real.exp (-8 * (r j).2.val / b)) else 0

private noncomputable def partnerWeight (t b : ℝ) (c : MarksCell) : ℝ≥0∞ :=
  if c.1.val ≤ t ∧ b < c.2.val then ENNReal.ofReal (Real.exp (-8 * c.2.val / b)) else 0

private theorem measurable_partnerWeight (t b : ℝ) : Measurable (partnerWeight t b) := by
  unfold partnerWeight
  apply Measurable.ite
  · exact (measurableSet_le (measurable_subtype_coe.comp measurable_fst) measurable_const).inter
      (measurableSet_lt measurable_const (measurable_subtype_coe.comp measurable_snd))
  · fun_prop
  · exact measurable_const

private theorem rowWeight_eq {w : ℕ} (u : Fin w) (J : Finset (Fin w)) (v : Fin w → ℝ)
    (q t b : ℝ) (j : Fin w) (r : MarksRow w) :
    rowWeight u J v q t b j r =
      (tight u J v q t).indicator (fun _ ↦ (1 : ℝ≥0∞)) r * partnerWeight t b (r j) := by
  by_cases h : r ∈ tight u J v q t <;> simp [rowWeight, partnerWeight, h]

@[fun_prop]
theorem measurable_rowWeight {w : ℕ} (u : Fin w) (J : Finset (Fin w)) (v : Fin w → ℝ)
    (q t b : ℝ) (j : Fin w) : Measurable (rowWeight u J v q t b j) := by
  simp_rw [funext (rowWeight_eq u J v q t b j)]
  exact (measurable_const.indicator (measurableSet_tight u J v q t)).mul
    ((measurable_partnerWeight t b).comp (measurable_pi_apply j))

private theorem indep_tight_eval {w : ℕ} {u j : Fin w} {J : Finset (Fin w)} (v : Fin w → ℝ)
    (q t : ℝ) (hu : u ∉ J) (hj : j ∉ insert u J) :
    IndepFun ((tight u J v q t).indicator (fun _ ↦ (1 : ℝ≥0∞))) (fun r ↦ r j)
      (marksRowMeasure w) := by
  let S := insert u J
  let restore (z : S → MarksCell) : MarksRow w := fun k ↦ if hk : k ∈ S then z ⟨k,hk⟩ else 0
  have hrestore : Measurable restore := by
    apply measurable_pi_iff.mpr
    intro k
    by_cases hk : k ∈ S
    · simpa only [restore, dite_eq_left hk] using (measurable_pi_apply (⟨k,hk⟩ : S) : Measurable (fun z : S → MarksCell ↦ z ⟨k,hk⟩))
    · simp only [restore, dite_eq_right hk]
      exact measurable_const
  have hEq (r : MarksRow w) : restore (fun i : S ↦ r i) ∈ tight u J v q t ↔ r ∈ tight u J v q t := by
    rw [mem_tight hu, mem_tight hu]
    have heq (i : Fin w) (hi : i ∈ S) : restore (fun k : S ↦ r k) i = r i := dite_eq_left hi
    rw [heq u (Finset.mem_insert_self _ _)]
    apply or_congr_right
    apply exists_congr
    intro k
    apply and_congr_right
    intro hk
    rw [heq k (Finset.mem_insert_of_mem hk)]
  have hdisj : Disjoint S ({j} : Finset (Fin w)) := Finset.disjoint_singleton_right.mpr hj
  have hind := (indepFun_pi_restrict marksCellMeasure S {j} hdisj).comp
    ((measurable_const.indicator (measurableSet_tight u J v q t)).comp hrestore :
      Measurable ((tight u J v q t).indicator (fun _ ↦ (1 : ℝ≥0∞)) ∘ restore))
    (measurable_pi_apply (⟨j, Finset.mem_singleton_self j⟩ : ({j} : Finset (Fin w))) :
      Measurable (fun z : ({j} : Finset (Fin w)) → MarksCell ↦ z ⟨j, Finset.mem_singleton_self j⟩))
  have htind : (fun r : MarksRow w ↦ (tight u J v q t).indicator (fun _ ↦ (1 : ℝ≥0∞))
      (restore (fun k : S ↦ r k))) = (tight u J v q t).indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
    funext r
    by_cases h : r ∈ tight u J v q t
    · simp [h, (hEq r).mpr h]
    · simp [h, mt (hEq r).mp h]
  change IndepFun (fun r : MarksRow w ↦ (tight u J v q t).indicator (fun _ ↦ (1 : ℝ≥0∞))
    (restore (fun k : S ↦ r k))) (fun r ↦ r j) (marksRowMeasure w) at hind
  rwa [htind] at hind

/-- Integral of the retained fresh partner's firm mark and exponential worker weight. -/
theorem cellWeight_bound {t b : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hb : 0 < b) :
    (∫⁻ c : MarksCell, (if c.1.val ≤ t ∧ b < c.2.val then
      ENNReal.ofReal (Real.exp (-8*c.2.val/b)) else 0) ∂marksCellMeasure) ≤
      ENNReal.ofReal (t*b/8) := by
  let a : ℝ := -8 / b
  have ha : a < 0 := div_neg_of_neg_of_pos (by norm_num) hb
  let g (z : ℝ) := ENNReal.ofReal (Real.exp (a * z))
  have hg : Measurable g := by dsimp [g]; fun_prop
  let h (z : ℝ) := (Ioi (0 : ℝ)).indicator g z
  have hh : Measurable h := hg.indicator measurableSet_Ioi
  let f (x : unitInterval) : ℝ≥0∞ := (Iic (⟨t, ht⟩ : unitInterval)).indicator 1 x
  have hf : Measurable f := measurable_const.indicator measurableSet_Iic
  have hfi : ∫⁻ x, f x = ENNReal.ofReal t := by
    simp [f, lintegral_indicator measurableSet_Iic, unitInterval.volume_Iic]
  have hhi : (∫⁻ y : unitInterval, h y.val) ≤ ENNReal.ofReal (b/8) := by
    rw [unitInterval.measurePreserving_coe.lintegral_comp hh]
    unfold h
    rw [lintegral_indicator measurableSet_Ioi]
    refine (lintegral_mono' (Measure.restrict_mono_measure Measure.restrict_le_self _)
      (le_refl g)).trans ?_
    change (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (a*z))) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi ha 0)
      (ae_of_all _ (fun z ↦ (Real.exp_pos _).le)), integral_exp_mul_Ioi ha]
    simp only [mul_zero, Real.exp_zero]
    exact le_of_eq (congrArg ENNReal.ofReal (by dsimp [a]; field_simp))
  calc
    _ ≤ ∫⁻ c : MarksCell, f c.1 * h c.2.val ∂marksCellMeasure := by
      apply lintegral_mono
      intro c
      dsimp only
      split_ifs with hc
      · have hx : c.1 ∈ Iic (⟨t, ht⟩ : unitInterval) := hc.1
        have hy : c.2.val ∈ Ioi (0 : ℝ) := hb.trans hc.2
        simp [f, h, g, hx, hy, a]
        ring_nf
        exact le_rfl
      · exact bot_le
    _ = (∫⁻ x, f x) * ∫⁻ y : unitInterval, h y.val :=
      lintegral_prod_mul hf.aemeasurable (hh.comp measurable_subtype_coe).aemeasurable
    _ ≤ ENNReal.ofReal (t*b/8) := by
      rw [hfi, mul_div_assoc, ENNReal.ofReal_mul ht.1]
      exact mul_le_mul_right hhi _

/-- The expected weight of one specified fresh worker bounds the cost of retaining its row. -/
theorem lintegral_rowWeight_le {w : ℕ} {u j : Fin w} {J : Finset (Fin w)} {v : Fin w → ℝ}
    {q t b : ℝ} (hu : u ∉ J) (hj : j ∉ insert u J)
    (hq : q ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hb : 0 < b)
    (hv : ∀ l ∈ J, v l ∈ Icc (0 : ℝ) 1) :
    (∫⁻ r, rowWeight u J v q t b j r ∂marksRowMeasure w) ≤
      ENNReal.ofReal (t ^ 2 * (1 + ∑ l ∈ J, v l) * b / 8) := by
  let μ := marksRowMeasure w
  let A := tight u J v q t
  have hA : MeasurableSet A := measurableSet_tight _ _ _ _ _
  have htight := measureReal_tight_le hu hq ht hv
  have hT : μ A ≤ ENNReal.ofReal (t * (1 + ∑ l ∈ J, v l)) := by
    simpa only [μ, A, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      (ENNReal.ofReal_le_ofReal htight)
  have hind := (indep_tight_eval v q t hu hj).comp measurable_id (measurable_partnerWeight t b)
  have hi : IndepFun (A.indicator (fun _ ↦ (1 : ℝ≥0∞))) (fun r : MarksRow w ↦
      partnerWeight t b (r j)) μ := hind
  simp_rw [rowWeight_eq]
  have hfactor := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (measurable_const.indicator hA).aemeasurable
    ((measurable_partnerWeight t b).comp (measurable_pi_apply j)).aemeasurable hi
  simp only [Function.comp_apply] at hfactor
  change (∫⁻ r, A.indicator (fun _ ↦ (1 : ℝ≥0∞)) r * partnerWeight t b (r j) ∂μ) ≤ _
  rw [hfactor, lintegral_indicator hA]
  simp only [lintegral_const, Measure.restrict_apply_univ, one_mul]
  have heval : (∫⁻ r : MarksRow w, partnerWeight t b (r j) ∂μ) =
      ∫⁻ c, partnerWeight t b c ∂marksCellMeasure :=
    (measurePreserving_eval (fun _ : Fin w ↦ marksCellMeasure) j).lintegral_comp
      (measurable_partnerWeight t b)
  rw [heval]
  refine (mul_le_mul' hT (cellWeight_bound ht hb)).trans_eq ?_
  rw [← ENNReal.ofReal_mul]
  · congr 1
    ring
  · exact mul_nonneg ht.1 (add_nonneg zero_le_one (Finset.sum_nonneg fun i hi ↦ (hv i hi).1))

end WorkerCompromiseProof.Bounds.Paper
