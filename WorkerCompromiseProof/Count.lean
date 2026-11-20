/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import WorkerCompromiseProof.Slice
public import WorkerCompromiseProof.Core.AssignmentLaw
public import WorkerCompromiseProof.Core.Scales
public import WorkerCompromiseProof.Core.FirstMoment
public import WorkerCompromiseProof.Core.CascadeLimit

/-!
# The expected number of assignments passing both tests

For each fixed injection, integrate the probability of stability conditional on its
assigned marks. Linearity of the integral counts all qualifying stable assignments
without any independence assumption across assignments.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory Set SwitchingCostMatching Filter
open scoped ENNReal BigOperators Topology

/-- The contribution of an individual injection to the paper's count. -/
def qualifyingAssignment {n : ℕ} (q s b B : ℝ) (m : Matching n (n + 1)) :
    Set (MarksProfile n (n + 1)) :=
  {p | MarksStable (fun i j ↦ (p i j).1.val) (fun i j ↦ (p i j).2.val) q m ∧
    s ≤ (∑ i, (p i (m i)).1.val) ∧ B ≤ workerTailMass b (fun i ↦ (p i (m i)).2.val)}

private theorem measurableSet_qualifyingAssignment {n : ℕ} (q s b B : ℝ)
    (m : Matching n (n + 1)) : MeasurableSet (qualifyingAssignment q s b B m) := by
  unfold qualifyingAssignment
  rw [Set.ofPred_and, Set.ofPred_and]
  refine (measurableSet_marksStable m q).inter (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_le measurable_const (show Measurable
      (fun p : MarksProfile n (n + 1) ↦ ∑ i, (p i (m i)).1.val) by fun_prop)
  · exact measurableSet_le measurable_const (measurable_assignedWorkerTailMass m b)

/-- Number of qualifying stable assignments, expressed as the sum of their indicators. -/
noncomputable def stableAssignmentCount (n : ℕ) (q s b B : ℝ) (p : MarksProfile n (n + 1)) :
    ℝ≥0∞ :=
  ∑ m : Matching n (n + 1), (qualifyingAssignment q s b B m).indicator 1 p

open scoped Classical in
/-- The indicator sum is the cardinality of the finite set counted in the paper. -/
theorem stableAssignmentCount_eq_card (n : ℕ) (q s b B : ℝ) (p : MarksProfile n (n + 1)) :
    stableAssignmentCount n q s b B p =
      ((Finset.univ.filter (fun m : Matching n (n + 1) ↦ p ∈ qualifyingAssignment q s b B m)).card :
        ℝ≥0∞) := by
  simp [stableAssignmentCount, Set.indicator_apply]

/-- Expected count over ordinary markets in the uniform-mark representation. -/
noncomputable def expectedStableAssignmentCount (n : ℕ) (q s b B : ℝ) : ℝ≥0∞ :=
  ∫⁻ p, stableAssignmentCount n q s b B p ∂marksProfileMeasure n (n + 1)

/-- Linearity turns the expectation into a sum of assignment probabilities. -/
theorem expectedStableAssignmentCount_eq_sum (n : ℕ) (q s b B : ℝ) :
    expectedStableAssignmentCount n q s b B =
      ∑ m : Matching n (n + 1), marksProfileMeasure n (n + 1) (qualifyingAssignment q s b B m) := by
  unfold expectedStableAssignmentCount stableAssignmentCount
  rw [lintegral_finsetSum _ (fun m _ ↦ measurable_one.indicator
    (measurableSet_qualifyingAssignment q s b B m))]
  exact Finset.sum_congr rfl (fun m _ ↦
    lintegral_indicator_one (measurableSet_qualifyingAssignment q s b B m))

/-- If any stable assignment passes both tests, the count is at least one. -/
theorem measure_largeFirmScoreHeavyWorkerTail_le_expectedCount (n : ℕ) (q s b B : ℝ) :
    marksProfileMeasure n (n + 1) (largeFirmScoreHeavyWorkerTail n q s b B) ≤
      expectedStableAssignmentCount n q s b B := by
  have events : largeFirmScoreHeavyWorkerTail n q s b B =
      ⋃ m : Matching n (n + 1), qualifyingAssignment q s b B m := by
    ext p
    simp [largeFirmScoreHeavyWorkerTail, qualifyingAssignment]
  rw [events, expectedStableAssignmentCount_eq_sum]
  simpa only [tsum_fintype] using (measure_iUnion_le (μ := marksProfileMeasure n (n + 1))
    (fun m : Matching n (n + 1) ↦ qualifyingAssignment q s b B m))

private theorem lintegral_assignedCells_split {n : ℕ}
    {A B : Set (Fin n → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {f : (Fin n → ℝ) × (Fin n → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    let μ := Measure.pi (fun _ : Fin n ↦ volume.restrict (Icc (0 : ℝ) 1))
    (∫⁻ d : Fin n → MarksCell in
      {d | (fun i ↦ (d i).1.val) ∈ A ∧ (fun i ↦ (d i).2.val) ∈ B},
      f (fun i ↦ (d i).1.val, fun i ↦ (d i).2.val)
      ∂(Measure.pi (fun _ : Fin n ↦ marksCellMeasure))) =
      ∫⁻ x in A, ∫⁻ y in B, f (x, y) ∂μ ∂μ := by
  let μ₀ : Measure (Fin n → unitInterval) := Measure.pi (fun _ : Fin n ↦ volume)
  let μ : Measure (Fin n → ℝ) :=
    Measure.pi (fun _ : Fin n ↦ volume.restrict (Icc (0 : ℝ) 1))
  let coeMarks (x : Fin n → unitInterval) (i : Fin n) : ℝ := (x i).val
  have hcoe : MeasurePreserving coeMarks μ₀ μ :=
    measurePreserving_pi _ _ (fun _ ↦ unitInterval.measurePreserving_coe)
  have hsplit : MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow unitInterval unitInterval (Fin n))
      (Measure.pi (fun _ : Fin n ↦ marksCellMeasure)) (μ₀.prod μ₀) :=
    measurePreserving_arrowProdEquivProdArrow _ _ _ _ _
  have h := (hcoe.prod hcoe).comp hsplit
  change MeasurePreserving
    (fun d : Fin n → MarksCell ↦ (fun i ↦ (d i).1.val, fun i ↦ (d i).2.val))
    (Measure.pi (fun _ : Fin n ↦ marksCellMeasure)) (μ.prod μ) at h
  change (∫⁻ d : Fin n → MarksCell in
      (fun d : Fin n → MarksCell ↦ (fun i ↦ (d i).1.val, fun i ↦ (d i).2.val)) ⁻¹' (A ×ˢ B),
      f (fun i ↦ (d i).1.val, fun i ↦ (d i).2.val) ∂(Measure.pi (fun _ ↦ marksCellMeasure))) = _
  rw [h.setLIntegral_comp_preimage (hA.prod hB) hf, setLIntegral_prod _ hf.aemeasurable]

/-- Integral of the conditional stability probability over the prescribed firm and worker scores. -/
noncomputable def qualifyingAssignmentIntegral (n : ℕ) (q s b B : ℝ) : ℝ≥0∞ :=
  let μ := Measure.pi (fun _ : Fin n ↦ volume.restrict (Icc (0 : ℝ) 1))
  ∫⁻ x : Fin n → ℝ in {x | s ≤ ∑ i, x i},
    ∫⁻ y : Fin n → ℝ in {y | B ≤ workerTailMass b y},
      ENNReal.ofReal (vacancyStabilityProduct q x y) ∂μ ∂μ

/-- The two-score integral is the same for each specified injection. -/
theorem measure_qualifyingAssignment_eq_integral {n : ℕ} {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (s b B : ℝ) (m : Matching n (n + 1)) :
    marksProfileMeasure n (n + 1) (qualifyingAssignment q s b B m) =
      qualifyingAssignmentIntegral n q s b B := by
  let A : Set (Fin n → ℝ) := {x | s ≤ ∑ i, x i}
  let V : Set (Fin n → ℝ) := {y | B ≤ workerTailMass b y}
  have hA : MeasurableSet A := measurableSet_le measurable_const (by fun_prop)
  have hV : MeasurableSet V := measurableSet_le measurable_const (measurable_workerTailMass b)
  let dSet : Set (Fin n → MarksCell) :=
    {d | (fun i ↦ (d i).1.val) ∈ A ∧ (fun i ↦ (d i).2.val) ∈ V}
  have hdSet : MeasurableSet dSet :=
    (hA.preimage (by fun_prop)).inter (hV.preimage (by fun_prop))
  obtain ⟨u, hu⟩ := exists_unmatched m
  change marksProfileMeasure n (n + 1)
    {p | MarksStable (fun i j ↦ (p i j).1.val) (fun i j ↦ (p i j).2.val) q m ∧
      assignedCells m p ∈ dSet} = _
  rw [marksProfileMeasure_stable_assignedCells m u hu hq dSet hdSet]
  let f (p : (Fin n → ℝ) × (Fin n → ℝ)) :=
    ENNReal.ofReal (vacancyStabilityProduct q p.1 p.2)
  have hf : Measurable f := by
    unfold f vacancyStabilityProduct
    fun_prop
  change (∫⁻ d : Fin n → MarksCell in
      {d | (fun i ↦ (d i).1.val) ∈ A ∧ (fun i ↦ (d i).2.val) ∈ V},
      f (fun i ↦ (d i).1.val, fun i ↦ (d i).2.val)
      ∂(Measure.pi (fun _ ↦ marksCellMeasure))) = _
  rw [lintegral_assignedCells_split hA hV hf]
  rfl

private theorem card_compromiseInjections (n : ℕ) :
    Fintype.card (Matching n (n + 1)) = (n + 1) * n.factorial := by
  rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin,
    Nat.descFactorial_eq_div (Nat.le_succ _), show n.succ - n = 1 by omega]
  simp [Nat.factorial_succ]

/-- The market expectation equals the probability for one fixed injection times the exact
number of possible injections. -/
theorem expectedStableAssignmentCount_eq_factorial_mul {n : ℕ} {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (s b B : ℝ) :
    expectedStableAssignmentCount n q s b B =
      (↑((n + 1) * n.factorial) : ℝ≥0∞) * qualifyingAssignmentIntegral n q s b B := by
  rw [expectedStableAssignmentCount_eq_sum]
  simp only [measure_qualifyingAssignment_eq_integral hq, Finset.sum_const, Finset.card_univ,
    card_compromiseInjections, nsmul_eq_mul]

/-- The factorial counting the injections cancels the factorial in the simplex slice. -/
private theorem count_mul_slice {n : ℕ} {q s : ℝ} (hq : 0 < q) :
    (↑((n + 1 + 1) * (n + 1).factorial) : ℝ≥0∞) *
        ENNReal.ofReal ((q ^ 2)⁻¹ ^ (n + 1) * (Real.log (((n : ℝ) + 1) / s) / n.factorial)) =
      ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1) *
        Real.log (((n + 1 : ℕ) : ℝ) / s) * q ^ (-(2 * ((n + 1 : ℕ) : ℝ)))) := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  have hpow : q ^ (-(2 * ((n + 1 : ℕ) : ℝ))) = (q ^ 2)⁻¹ ^ (n + 1) := by
    rw [Real.rpow_neg hq.le, Real.rpow_mul hq.le]
    norm_cast
    rw [inv_pow]
  rw [hpow]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp

/-- Before tilting, the expected count is bounded by the simplex factor times the
probability of a tail event for independent rate-one exponential variables. -/
theorem expectedStableAssignmentCount_le_expTail {n : ℕ} {q s b B : ℝ} (hn : 0 < n)
    (hq : q ∈ Ioc (0 : ℝ) 1) (hs : 0 < s) (hsn : s ≤ (n : ℝ))
    (hb : 0 ≤ b) (hB : 0 ≤ B) :
    expectedStableAssignmentCount n q s b B ≤
      ENNReal.ofReal ((n : ℝ) * ((n : ℝ) + 1) * Real.log ((n : ℝ) / s) * q ^ (-(2 * (n : ℝ)))) *
        expTail (Fin n) (q ^ 2 * s) b B := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hsn' : s ≤ (n : ℝ) + 1 := by simpa using hsn
  rw [expectedStableAssignmentCount_eq_factorial_mul ⟨hq.1.le, hq.2⟩]
  apply (mul_le_mul_right (fixedInjection_lintegral_le_expTail n hq hs hsn' hb hB)
    (↑((n + 1 + 1) * (n + 1).factorial) : ℝ≥0∞)).trans_eq
  rw [mul_left_comm, count_mul_slice hq.1, mul_comm]

/-- Exponential Markov applied at the smallest admissible firm sum. -/
theorem expectedStableAssignmentCount_le {n : ℕ} {q s b B : ℝ} (hn : 0 < n)
    (hq : q ∈ Ioc (0 : ℝ) 1) (hs : 0 < s) (hsn : s ≤ (n : ℝ))
    (hb : 0 ≤ b) (hB : 0 ≤ B) :
    expectedStableAssignmentCount n q s b B ≤
      ENNReal.ofReal ((n : ℝ) * ((n : ℝ) + 1) * Real.log ((n : ℝ) / s) *
        q ^ (-(2 * (n : ℝ))) * Real.exp (-(q ^ 2 * s * B) / 2) *
        (1 + 2 * Real.exp (-(q ^ 2 * s * b) / 2)) ^ n) := by
  apply (expectedStableAssignmentCount_le_expTail hn hq hs hsn hb hB).trans
  have ht := measure_exponentialWorkerTail_le (ι := Fin n)
    (a := q ^ 2 * s * b) (d := q ^ 2 * s * B) (mul_nonneg (mul_nonneg (sq_nonneg q) hs.le) hb)
  change expTail (Fin n) (q ^ 2 * s) b B ≤ _ at ht
  apply (mul_le_mul_right ht _).trans_eq
  have hl : 0 ≤ Real.log ((n : ℝ) / s) := Real.log_nonneg ((le_div_iff₀ hs).mpr (by simpa using hsn))
  have hp := hq.1
  rw [Fintype.card_fin, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- The fixed-injection bound in the scales used by the asymptotic disproof. -/
theorem eventually_expectedStableAssignmentCount_le_annealedEnvelope :
    ∀ᶠ n : ℕ in atTop,
      expectedStableAssignmentCount n (compromiseQ n) (firmScoreCutoff n)
          (workerMarkCutoff n) (historyGrowthTarget n - 1) ≤
        ENNReal.ofReal (annealedEnvelope n) := by
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hp : 0 < (n : ℝ) := zero_lt_one.trans_le hnR
  have hq : compromiseQ n ∈ Ioc (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, compromiseQ_le_one n⟩
  have hs : 0 < firmScoreCutoff n := Real.rpow_pos_of_pos hp _
  have hsn : firmScoreCutoff n ≤ (n : ℝ) := by
    calc
      firmScoreCutoff n ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
      _ = _ := Real.rpow_one _
  have hb : 0 ≤ workerMarkCutoff n := Real.rpow_nonneg hp.le _
  have hB : 0 ≤ historyGrowthTarget n - 1 :=
    sub_nonneg.mpr (Real.one_le_rpow hnR (by norm_num))
  exact expectedStableAssignmentCount_le (by omega) hq hs hsn hb hB

/-- The expected count tends to zero at the paper's cutoffs. -/
theorem tendsto_expectedStableAssignmentCount_zero :
    Tendsto (fun n : ℕ ↦ expectedStableAssignmentCount n (compromiseQ n) (firmScoreCutoff n)
      (workerMarkCutoff n) (historyGrowthTarget n - 1)) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
    (Eventually.of_forall fun _ ↦ zero_le) eventually_expectedStableAssignmentCount_le_annealedEnvelope
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal tendsto_annealedEnvelope_zero

end WorkerCompromiseProof.Bounds.Paper
