module

public import WorkerCompromiseProof.Scores
public import WorkerCompromiseProof.RankMoment
public import WorkerCompromiseProof.EdgeLaw

/-!
# The exponential moment of the joint edge score

The firm evaluation is independent of the entire worker column. Within that column,
utility and rank may be dependent. Bounding the maximum by the sum after exponentiation
therefore gives a uniform moment estimate for each edge.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory ProbabilityTheory SwitchingCostMatching

private theorem worker_exp_le_add (u r t : ℝ) :
    Real.exp (t * max u r) ≤ Real.exp (t * u) + Real.exp (t * r) := by
  rcases le_total u r with h | h
  · simpa [max_eq_right h] using (le_add_of_nonneg_left (Real.exp_pos (t * u)).le :
      Real.exp (t * r) ≤ Real.exp (t * u) + Real.exp (t * r))
  · simpa [max_eq_left h] using (le_add_of_nonneg_right (Real.exp_pos (t * r)).le :
      Real.exp (t * u) ≤ Real.exp (t * u) + Real.exp (t * r))

private theorem edge_exp_estimates {n w : ℕ} (i : Fin n) (j : Fin w) {t : ℝ}
    (ht : 0 < t) (ht1 : t < 1) :
    Integrable (fun p : Profile n w ↦ Real.exp (t * (p (false, i, j) + workerScore p i j)))
      (profileMeasureWithWorkers n w) ∧
      (∫ p : Profile n w, Real.exp (t * (p (false, i, j) + workerScore p i j))
        ∂profileMeasureWithWorkers n w) ≤ 2 / (1 - t)^2 := by
  let μ := profileMeasureWithWorkers n w
  let col (p : Profile n w) (k : Fin n) := p (true, k, j)
  let a (p : Profile n w) := Real.exp (t * p (false, i, j))
  let v (p : Profile n w) := Real.exp (t * p (true, i, j))
  let r (p : Profile n w) := columnRankMoment i t (col p)
  let g (p : Profile n w) := Real.exp (t * workerScore p i j)
  have ha : Integrable a μ := integrable_exp_edgeUtility (false, i, j) ht1
  have hv : Integrable v μ := integrable_exp_edgeUtility (true, i, j) ht1
  have hcol : MeasurePreserving col μ (Measure.pi fun _ : Fin n ↦ expMeasure 1) :=
    measurePreserving_workerColumn j
  have hr : Integrable r μ := hcol.integrable_comp_of_integrable
    (integrable_columnRankMoment i ht.le)
  have hgr (p : Profile n w) : g p ≤ v p + r p := worker_exp_le_add _ _ _
  have hg : Integrable g μ := (hv.add hr).mono' (((measurable_workerScore i j).const_mul t).exp
    |>.aestronglyMeasurable) (ae_of_all _ fun p ↦ by
      simpa only [g, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Pi.add_apply] using hgr p)
  have hw : Measurable (fun y : Fin n → ℝ ↦ Real.exp (t * max (y i)
      (Real.log ((n : ℝ) / Imbalanced.inclusiveColumnRank i y)))) :=
    (((measurable_pi_apply i).max ((Measurable.of_discrete (f := fun k : ℕ ↦
      Real.log ((n : ℝ) / k))).comp (Imbalanced.measurable_inclusiveColumnRank i))).const_mul t).exp
  have hag : IndepFun a g μ := (indepFun_firm_workerColumn i j).comp
    (((measurable_id' : Measurable (fun x : ℝ ↦ x)).const_mul t).exp) hw
  have had : (∫ p, a p ∂μ) = (1 - t)⁻¹ := integral_exp_edgeUtility (false, i, j) ht1
  have hvd : (∫ p, v p ∂μ) = (1 - t)⁻¹ := integral_exp_edgeUtility (true, i, j) ht1
  have hrd : (∫ p, r p ∂μ) ≤ (1 - t)⁻¹ := calc
    _ = ∫ y, columnRankMoment i t y ∂Measure.pi (fun _ : Fin n ↦ expMeasure 1) := by
      rw [← hcol.map_eq, integral_map hcol.measurable.aemeasurable
        (measurable_columnRankMoment i t).aestronglyMeasurable]
    _ ≤ _ := integral_columnRankMoment_le i ht ht1
  have hgd := (integral_mono hg (hv.add hr) hgr).trans_eq
    (integral_add hv hr)
  have heq : (fun p : Profile n w ↦ Real.exp (t * (p (false, i, j) + workerScore p i j)))
      = fun p ↦ a p * g p := by
    funext p
    rw [mul_add, Real.exp_add]
  rw [heq]
  refine ⟨hag.integrable_mul ha hg, ?_⟩
  rw [hag.integral_fun_mul_eq_mul_integral ha.aestronglyMeasurable hg.aestronglyMeasurable, had]
  have hnon : 0 ≤ (1 - t)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr ht1.le)
  calc
    _ ≤ (1 - t)⁻¹ * ((1-t)⁻¹ + (1-t)⁻¹) := mul_le_mul_of_nonneg_left
      (hgd.trans (add_le_add hvd.le hrd)) hnon
    _ = _ := by rw [div_eq_mul_inv, ← inv_pow]; ring

/-- Integrability of the joint firm and worker exponential score on a fixed edge. -/
theorem integrable_exp_edgeScore {n w : ℕ} (i : Fin n) (j : Fin w) {t : ℝ}
    (ht : 0 < t) (ht1 : t < 1) :
    Integrable (fun p : Profile n w ↦ Real.exp (t * (p (false, i, j) + workerScore p i j)))
      (profileMeasureWithWorkers n w) := (edge_exp_estimates i j ht ht1).1

/-- The joint edge moment costs at most two independent exponential moment factors. -/
theorem integral_exp_edgeScore_le {n w : ℕ} (i : Fin n) (j : Fin w) {t : ℝ}
    (ht : 0 < t) (ht1 : t < 1) :
    (∫ p : Profile n w, Real.exp (t * (p (false, i, j) + workerScore p i j))
      ∂profileMeasureWithWorkers n w) ≤ 2 / (1 - t)^2 := (edge_exp_estimates i j ht ht1).2

/-- Nonnegative-integral version of the edge bound. -/
theorem lintegral_exp_edgeScore_le {n w : ℕ} (i : Fin n) (j : Fin w) {t : ℝ}
    (ht : 0 < t) (ht1 : t < 1) :
    (∫⁻ p : Profile n w, ENNReal.ofReal (Real.exp (t * (p (false, i, j) + workerScore p i j)))
      ∂profileMeasureWithWorkers n w) ≤ ENNReal.ofReal (2 / (1 - t)^2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_edgeScore i j ht ht1)
    (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal (integral_exp_edgeScore_le i j ht ht1)

end WorkerCompromiseProof.Bounds.Paper
