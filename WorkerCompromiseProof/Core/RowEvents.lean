/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib

/-!
# Row events in the one-extra-worker disproof

The finite history argument uses independent uniform tail marks. Within each row, the marks
for a previously recorded worker and the marks for a new partner lie in different columns.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

/-- Firm and worker tail marks on one edge. -/
abbrev MarksCell := unitInterval × unitInterval

/-- The tail marks for one firm's row. -/
abbrev MarksRow (w : ℕ) := Fin w → MarksCell

/-- The complete array of tail marks. -/
abbrev MarksProfile (n w : ℕ) := Fin n → MarksRow w

/-- Independent uniform firm and worker marks on an edge. -/
noncomputable def marksCellMeasure : Measure MarksCell :=
  (volume : Measure unitInterval).prod volume

instance : IsProbabilityMeasure marksCellMeasure := by
  unfold marksCellMeasure
  infer_instance

/-- Independent columns in one firm's row. -/
noncomputable def marksRowMeasure (w : ℕ) : Measure (MarksRow w) :=
  Measure.pi fun _ ↦ marksCellMeasure

instance (w : ℕ) : IsProbabilityMeasure (marksRowMeasure w) := by
  unfold marksRowMeasure
  infer_instance

/-- Independent rows of the market. -/
noncomputable def marksProfileMeasure (n w : ℕ) : Measure (MarksProfile n w) :=
  Measure.pi fun _ ↦ marksRowMeasure w

/-- Finite cylinder probabilities multiply under the product law. -/
theorem measureReal_pi_finset_const {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι) (a : ι → Set Ω) :
    (Measure.pi (fun _ : ι ↦ μ)).real ((s : Set ι).pi a) = ∏ i ∈ s, μ.real (a i) := by
  simp [measureReal_def, Measure.pi_pi_finset, ENNReal.toReal_prod]

/-- Restrictions to disjoint coordinate sets are independent under the finite product law. -/
theorem indepFun_pi_restrict {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s t : Finset ι) (h : Disjoint s t) :
    IndepFun (fun (x : ι → Ω) (i : s) ↦ x i) (fun (x : ι → Ω) (i : t) ↦ x i)
      (Measure.pi fun _ : ι ↦ μ) := by
  have hi := iIndepFun_pi (μ := fun _ : ι ↦ μ) (X := fun _ ↦ id)
    (fun _ ↦ measurable_id.aemeasurable)
  exact hi.indepFun_finset s t h (fun i ↦ measurable_pi_apply i)

/-- Real-valued probabilities of events on disjoint coordinates multiply. -/
theorem measureReal_inter_restrict {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s t : Finset ι) (h : Disjoint s t)
    (a : Set (s → Ω)) (b : Set (t → Ω)) (ha : MeasurableSet a) (hb : MeasurableSet b) :
    let ν := Measure.pi fun _ : ι ↦ μ
    let A := (fun (x : ι → Ω) (i : s) ↦ x i) ⁻¹' a
    let B := (fun (x : ι → Ω) (i : t) ↦ x i) ⁻¹' b
    ν.real (A ∩ B) = ν.real A * ν.real B := by
  dsimp only
  simp only [measureReal_def, (indepFun_pi_restrict μ s t h).measure_inter_preimage_eq_mul a b ha hb,
    ENNReal.toReal_mul]

def below (r : ℝ) : Set unitInterval := {x | (x : ℝ) < r}
def atMost (r : ℝ) : Set unitInterval := {x | (x : ℝ) ≤ r}

private theorem measurableSet_below (r : ℝ) : MeasurableSet (below r) :=
  measurableSet_lt measurable_subtype_coe measurable_const

private theorem measurableSet_atMost (r : ℝ) : MeasurableSet (atMost r) :=
  measurableSet_le measurable_subtype_coe measurable_const

private theorem volumeReal_below {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    (volume : Measure unitInterval).real (below r) = r := by
  let a : unitInterval := ⟨r, h0, h1⟩
  change (volume : Measure unitInterval).real (Iio a) = r
  simp [measureReal_def, a, ENNReal.toReal_ofReal h0]

private theorem volumeReal_atMost {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    (volume : Measure unitInterval).real (atMost r) = r := by
  let a : unitInterval := ⟨r, h0, h1⟩
  change (volume : Measure unitInterval).real (Iic a) = r
  simp [measureReal_def, a, ENNReal.toReal_ofReal h0]

def quietColumn {w : ℕ} (u : Fin w) (v : Fin w → ℝ) (q t : ℝ) (j : Fin w) :
    Set MarksCell :=
  if j = u then (below (q * t) ×ˢ univ)ᶜ else (below (q * t) ×ˢ below (q * v j))ᶜ

private theorem measurableSet_quietColumn {w : ℕ} (u : Fin w) (v : Fin w → ℝ) (q t : ℝ)
    (j : Fin w) : MeasurableSet (quietColumn u v q t j) := by
  unfold quietColumn
  split
  · exact ((measurableSet_below _).prod MeasurableSet.univ).compl
  · exact ((measurableSet_below _).prod (measurableSet_below _)).compl

/-- The vacancy or an old partner forces the firm mark below the cutoff. -/
def tight {w : ℕ} (u : Fin w) (J : Finset (Fin w)) (v : Fin w → ℝ) (q t : ℝ) :
    Set (MarksRow w) :=
  ((↑(insert u J) : Set (Fin w)).pi (quietColumn u v q t))ᶜ

/-- All unrecorded nonvacant columns lack a good edge in this row. -/
def noGood {w : ℕ} (u : Fin w) (J : Finset (Fin w)) (t b : ℝ) : Set (MarksRow w) :=
  (↑(Finset.univ \ insert u J) : Set (Fin w)).pi (fun _ ↦ (atMost t ×ˢ atMost b)ᶜ)

/-- Both tests of a forced row. -/
def forcedRowsEvent {w : ℕ} (u : Fin w) (J : Finset (Fin w)) (v : Fin w → ℝ)
    (q t b : ℝ) : Set (MarksRow w) :=
  tight u J v q t ∩ noGood u J t b

theorem mem_tight {w : ℕ} {u : Fin w} {J : Finset (Fin w)} {v : Fin w → ℝ} {q t : ℝ}
    {x : MarksRow w} (hu : u ∉ J) :
    x ∈ tight u J v q t ↔
      (x u).1.val < q * t ∨ ∃ j ∈ J, (x j).1.val < q * t ∧ (x j).2.val < q * v j := by
  classical
  simp only [tight, Set.mem_compl_iff, Set.mem_pi, Finset.mem_coe, Finset.mem_insert]
  push Not
  constructor
  · rintro ⟨j, rfl | hj, hj'⟩
    · exact Or.inl (by simpa [quietColumn, below] using hj')
    · have hju : j ≠ u := fun h ↦ hu (h ▸ hj)
      exact Or.inr ⟨j, hj, by simpa [quietColumn, hju, below] using hj'⟩
  · rintro (hx | ⟨j, hj, hx⟩)
    · exact ⟨u, Or.inl rfl, by simpa [quietColumn, below] using hx⟩
    · have hju : j ≠ u := fun h ↦ hu (h ▸ hj)
      exact ⟨j, Or.inr hj, by simpa [quietColumn, hju, below] using hx⟩

theorem mem_noGood {w : ℕ} {u : Fin w} {J : Finset (Fin w)} {t b : ℝ} {x : MarksRow w} :
    x ∈ noGood u J t b ↔
      ∀ j, j ≠ u → j ∉ J → ¬ ((x j).1.val ≤ t ∧ (x j).2.val ≤ b) := by
  simp [noGood, atMost, Set.mem_pi, not_or, and_imp, ne_comm]

private theorem measurableSet_finset_pi {ι Ω : Type*} [MeasurableSpace Ω] (s : Finset ι)
    (a : ι → Set Ω) (h : ∀ i, MeasurableSet (a i)) : MeasurableSet ((s : Set ι).pi a) :=
  MeasurableSet.pi (s.finite_toSet.countable) fun i _ ↦ h i

theorem measurableSet_tight {w : ℕ} (u : Fin w) (J : Finset (Fin w)) (v : Fin w → ℝ)
    (q t : ℝ) : MeasurableSet (tight u J v q t) :=
  (measurableSet_finset_pi _ _ (measurableSet_quietColumn u v q t)).compl

theorem measurableSet_noGood {w : ℕ} (u : Fin w) (J : Finset (Fin w)) (t b : ℝ) :
    MeasurableSet (noGood u J t b) :=
  measurableSet_finset_pi _ _ (fun _ ↦
    ((measurableSet_atMost t).prod (measurableSet_atMost b)).compl)

theorem measurableSet_forcedRowsEvent {w : ℕ} (u : Fin w) (J : Finset (Fin w))
    (v : Fin w → ℝ) (q t b : ℝ) : MeasurableSet (forcedRowsEvent u J v q t b) :=
  (measurableSet_tight u J v q t).inter (measurableSet_noGood u J t b)

private theorem measureReal_inter_compl_pi_pi {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s t : Finset ι) (h : Disjoint s t)
    (a b : ι → Set Ω) (ha : ∀ i, MeasurableSet (a i)) (hb : ∀ i, MeasurableSet (b i)) :
    let ν := Measure.pi fun _ : ι ↦ μ
    ν.real (((s : Set ι).pi a)ᶜ ∩ (t : Set ι).pi b) =
      ν.real (((s : Set ι).pi a)ᶜ) * ν.real ((t : Set ι).pi b) := by
  have hpre (r : Finset ι) (c : ι → Set Ω) :
      (fun (x : ι → Ω) (i : r) ↦ x i) ⁻¹' ((univ : Set r).pi fun i ↦ c i) =
        (r : Set ι).pi c := by
    ext x
    simp [Set.mem_pi]
  simpa only [Set.preimage_compl, hpre] using
    measureReal_inter_restrict μ s t h
      (((univ : Set s).pi fun i ↦ a i)ᶜ) ((univ : Set t).pi fun i ↦ b i)
      (MeasurableSet.pi (countable_univ (α := s)) (fun i _ ↦ ha i)).compl
      (MeasurableSet.pi (countable_univ (α := t)) (fun i _ ↦ hb i))

private def tightColumnProbability {w : ℕ} (u : Fin w) (v : Fin w → ℝ) (q t : ℝ)
    (j : Fin w) : ℝ :=
  if j = u then q * t else q ^ 2 * t * v j

private theorem measureReal_quietColumn {w : ℕ} (u : Fin w) (v : Fin w → ℝ) (q t : ℝ)
    (j : Fin w) (hqt : q * t ∈ Icc (0 : ℝ) 1) (hqv : j ≠ u → q * v j ∈ Icc (0 : ℝ) 1) :
    marksCellMeasure.real (quietColumn u v q t j) = 1 - tightColumnProbability u v q t j := by
  by_cases hju : j = u
  · simp only [quietColumn, tightColumnProbability, hju, ite_true, marksCellMeasure]
    rw [measureReal_compl ((measurableSet_below _).prod MeasurableSet.univ),
      measureReal_prod_prod, volumeReal_below hqt.1 hqt.2]
    simp
  · simp only [quietColumn, tightColumnProbability, hju, ite_false, marksCellMeasure]
    rw [measureReal_compl ((measurableSet_below _).prod (measurableSet_below _)),
      measureReal_prod_prod, volumeReal_below hqt.1 hqt.2,
      volumeReal_below (hqv hju).1 (hqv hju).2]
    simp only [probReal_univ]
    ring

private theorem measureReal_tight {w : ℕ} (u : Fin w) (J : Finset (Fin w)) (v : Fin w → ℝ)
    (q t : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hv : ∀ j ∈ J, v j ∈ Icc (0 : ℝ) 1) :
    (marksRowMeasure w).real (tight u J v q t) =
      1 - ∏ j ∈ insert u J, (1 - tightColumnProbability u v q t j) := by
  unfold tight
  rw [measureReal_compl (measurableSet_finset_pi _ _ (measurableSet_quietColumn u v q t)),
    probReal_univ, marksRowMeasure, measureReal_pi_finset_const]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  apply measureReal_quietColumn
  · exact ⟨mul_nonneg hq.1 ht.1, (mul_le_of_le_one_left ht.1 hq.2).trans ht.2⟩
  · intro hju
    have h := hv j ((Finset.mem_insert.mp hj).resolve_left hju)
    exact ⟨mul_nonneg hq.1 h.1, (mul_le_of_le_one_left h.1 hq.2).trans h.2⟩

private theorem sum_tightColumnProbability {w : ℕ} (u : Fin w) (J : Finset (Fin w))
    (v : Fin w → ℝ) (q t : ℝ) (hu : u ∉ J) :
    ∑ j ∈ insert u J, tightColumnProbability u v q t j =
      q * t + q ^ 2 * t * ∑ j ∈ J, v j := by
  rw [Finset.sum_insert hu, Finset.mul_sum]
  congr 1
  · simp [tightColumnProbability]
  · apply Finset.sum_congr rfl
    intro j hj
    have hju : j ≠ u := fun h ↦ hu (h ▸ hj)
    simp [tightColumnProbability, hju]

private theorem one_sub_prod_one_sub_le_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, a i ∈ Icc (0 : ℝ) 1) :
    1 - ∏ i ∈ s, (1 - a i) ≤ ∑ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hai := ha i (Finset.mem_insert_self i s)
    have hs : ∀ j ∈ s, a j ∈ Icc (0 : ℝ) 1 := fun j hj ↦ ha j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    calc
      1 - (1 - a i) * ∏ j ∈ s, (1 - a j) =
          a i + (1 - a i) * (1 - ∏ j ∈ s, (1 - a j)) := by ring
      _ ≤ a i + (1 - a i) * ∑ j ∈ s, a j :=
        add_le_add_right (mul_le_mul_of_nonneg_left (ih hs) (sub_nonneg.mpr hai.2)) _
      _ ≤ a i + ∑ j ∈ s, a j := by
        have hsum : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg fun j hj ↦ (hs j hj).1
        have hmul := mul_le_mul_of_nonneg_right (show 1 - a i ≤ 1 by linarith [hai.1]) hsum
        simpa only [one_mul] using add_le_add_right hmul (a i)

private theorem tightColumnProbability_mem_Icc {w : ℕ} {u : Fin w} {J : Finset (Fin w)}
    {v : Fin w → ℝ} {q t : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hv : ∀ j ∈ J, v j ∈ Icc (0 : ℝ) 1) (j : Fin w) (hj : j ∈ insert u J) :
    tightColumnProbability u v q t j ∈ Icc (0 : ℝ) 1 := by
  have hqt : q * t ∈ Icc (0 : ℝ) 1 := ⟨mul_nonneg hq.1 ht.1, (mul_le_of_le_one_left ht.1 hq.2).trans ht.2⟩
  by_cases hju : j = u
  · simpa [tightColumnProbability, hju] using hqt
  · have h := hv j ((Finset.mem_insert.mp hj).resolve_left hju)
    have hqv : q * v j ∈ Icc (0 : ℝ) 1 := ⟨mul_nonneg hq.1 h.1, (mul_le_of_le_one_left h.1 hq.2).trans h.2⟩
    have he : q ^ 2 * t * v j = (q * t) * (q * v j) := by ring
    rw [tightColumnProbability, ite_eq_right hju, he]
    exact ⟨mul_nonneg hqt.1 hqv.1, (mul_le_of_le_one_left hqv.1 hqt.2).trans hqv.2⟩

private theorem tightColumnProbability_sum_le {w : ℕ} {u : Fin w} {J : Finset (Fin w)}
    {v : Fin w → ℝ} {q t : ℝ} (hu : u ∉ J) (hq : q ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hv : ∀ j ∈ J, v j ∈ Icc (0 : ℝ) 1) :
    ∑ j ∈ insert u J, tightColumnProbability u v q t j ≤ t * (1 + ∑ j ∈ J, v j) := by
  have hn : 0 ≤ ∑ j ∈ J, v j := Finset.sum_nonneg fun j hj ↦ (hv j hj).1
  rw [sum_tightColumnProbability u J v q t hu, mul_add, mul_one]
  apply add_le_add (mul_le_of_le_one_left ht.1 hq.2)
  have hq2 : q ^ 2 ≤ 1 := by nlinarith [mul_nonneg hq.1 (sub_nonneg.mpr hq.2)]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left ht.1 hq2) hn

/-- The first row test has probability at most the cutoff times the recorded mass. -/
theorem measureReal_tight_le {w : ℕ} {u : Fin w} {J : Finset (Fin w)} {v : Fin w → ℝ}
    {q t : ℝ} (hu : u ∉ J) (hq : q ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hv : ∀ j ∈ J, v j ∈ Icc (0 : ℝ) 1) :
    (marksRowMeasure w).real (tight u J v q t) ≤ t * (1 + ∑ j ∈ J, v j) := by
  rw [measureReal_tight u J v q t hq ht hv]
  exact (one_sub_prod_one_sub_le_sum _ _ (tightColumnProbability_mem_Icc hq ht hv)).trans
    (tightColumnProbability_sum_le hu hq ht hv)

private theorem one_sub_exp_neg_ge_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have hpos : 0 < 1 + x := by positivity
  have he : Real.exp (-x) * (1 + x) ≤ 1 := calc
    Real.exp (-x) * (1 + x) ≤ Real.exp (-x) * Real.exp x :=
      mul_le_mul_of_nonneg_left (by simpa only [add_comm x 1] using Real.add_one_le_exp x) (by positivity)
    _ = 1 := by rw [← Real.exp_add]; simp
  have hdiv : Real.exp (-x) ≤ 1 / (1 + x) := (le_div_iff₀ hpos).2 he
  have hb : 1 / (1 + x) ≤ 1 - x / 2 := by
    apply (div_le_iff₀ hpos).2
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  linarith [hdiv.trans hb]

/-- A lower bound for the first row test when the total hazard is small. -/
theorem measureReal_tight_lower {w : ℕ} {u : Fin w} {J : Finset (Fin w)} {v : Fin w → ℝ}
    {q t : ℝ} (hu : u ∉ J) (hq : q ∈ Icc (1 / 2 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hv : ∀ j ∈ J, v j ∈ Icc (0 : ℝ) 1) (hsmall : t * (1 + ∑ j ∈ J, v j) ≤ 1) :
    t * (1 + ∑ j ∈ J, v j) / 8 ≤ (marksRowMeasure w).real (tight u J v q t) := by
  let a := tightColumnProbability u v q t
  let s := insert u J
  let L := ∑ j ∈ s, a j
  have hq' : q ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hq.1], hq.2⟩
  have ha := tightColumnProbability_mem_Icc (u := u) hq' ht hv
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun j hj ↦ (ha j hj).1
  have hL1 : L ≤ 1 := (tightColumnProbability_sum_le hu hq' ht hv).trans hsmall
  have hL : t * (1 + ∑ j ∈ J, v j) / 4 ≤ L := by
    have hn : 0 ≤ ∑ j ∈ J, v j := Finset.sum_nonneg fun j hj ↦ (hv j hj).1
    have hq2 : (1 / 4 : ℝ) ≤ q ^ 2 := by nlinarith [hq.1, sq_nonneg (q - 1 / 2)]
    dsimp only [L, s, a]
    rw [sum_tightColumnProbability u J v q t hu]
    have hx := mul_le_mul_of_nonneg_right (show (1 / 4 : ℝ) ≤ q by linarith [hq.1]) ht.1
    have hy := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq2 ht.1) hn
    linarith
  have hprod : ∏ j ∈ s, (1 - a j) ≤ Real.exp (-L) := calc
    _ ≤ ∏ j ∈ s, Real.exp (-a j) := Finset.prod_le_prod₀
      (fun j hj ↦ sub_nonneg.mpr (ha j hj).2) (fun j _ ↦ Real.one_sub_le_exp_neg (a j))
    _ = _ := by rw [← Real.exp_sum, Finset.sum_neg_distrib]
  rw [measureReal_tight u J v q t hq' ht hv]
  change _ ≤ 1 - ∏ j ∈ s, (1 - a j)
  linarith [one_sub_exp_neg_ge_half hL0 hL1]

/-- The probability of the second row test. -/
theorem measureReal_noGood {w : ℕ} (u : Fin w) (J : Finset (Fin w)) {t b : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    (marksRowMeasure w).real (noGood u J t b) =
      (1 - t * b) ^ (Finset.univ \ insert u J).card := by
  rw [noGood, marksRowMeasure, measureReal_pi_finset_const]
  have hc : marksCellMeasure.real (atMost t ×ˢ atMost b)ᶜ = 1 - t * b := by
    rw [measureReal_compl ((measurableSet_atMost t).prod (measurableSet_atMost b)),
      probReal_univ, marksCellMeasure, measureReal_prod_prod,
      volumeReal_atMost ht.1 ht.2, volumeReal_atMost hb.1 hb.2]
  simp only [hc, Finset.prod_const]

/-- A forced row is the intersection of two independent tests on disjoint columns. -/
theorem measureReal_forcedRowsEvent {w : ℕ} (u : Fin w) (J : Finset (Fin w))
    (v : Fin w → ℝ) (q t b : ℝ) :
    (marksRowMeasure w).real (forcedRowsEvent u J v q t b) =
      (marksRowMeasure w).real (tight u J v q t) * (marksRowMeasure w).real (noGood u J t b) := by
  exact measureReal_inter_compl_pi_pi marksCellMeasure (insert u J)
    (Finset.univ \ insert u J) Finset.disjoint_sdiff
    (quietColumn u v q t) (fun _ ↦ (atMost t ×ˢ atMost b)ᶜ)
    (measurableSet_quietColumn u v q t)
    (fun _ ↦ ((measurableSet_atMost t).prod (measurableSet_atMost b)).compl)

private theorem quarter_le_pow_one_sub_inv {n : ℕ} (hn : 2 ≤ n) :
    1 / 4 ≤ (1 - 1 / (n : ℝ)) ^ n := by
  have hn' : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by positivity
  have hx : (0 : ℝ) ≤ 1 - 1 / n := by
    exact sub_nonneg.mpr ((div_le_iff₀ hn0).2 (by linarith))
  have hhalf : (1 / 2 : ℝ) ≤ (1 - 1 / n) ^ ((n : ℝ) / 2) := by
    have h := one_add_mul_self_le_rpow_one_add (s := -(1 / (n : ℝ)))
      (p := (n : ℝ) / 2) (by linarith) (by linarith)
    have hs : 1 + (n : ℝ) / 2 * -(1 / (n : ℝ)) = 1 / 2 := by
      field_simp
      norm_num
    rw [hs, ← sub_eq_add_neg] at h
    exact h
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 / 2 by norm_num) hhalf 2
  rw [← Real.rpow_mul_natCast hx] at hp
  norm_num only [Nat.cast_ofNat, show (n : ℝ) / 2 * 2 = n by ring, Real.rpow_natCast] at hp
  linarith

/-- Concrete lower bound used by the forced-row count for one extra worker. -/
theorem measureReal_forcedRowsEvent_lower {n : ℕ} {u : Fin (n + 1)}
    {J : Finset (Fin (n + 1))} {v : Fin (n + 1) → ℝ} {q t b : ℝ} (hn : 2 ≤ n)
    (hu : u ∉ J) (hq : q ∈ Icc (1 / 2 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (htb : t * b = 1 / (n : ℝ))
    (hv : ∀ j ∈ J, v j ∈ Icc (0 : ℝ) 1) (hsmall : t * (1 + ∑ j ∈ J, v j) ≤ 1) :
    t * (1 + ∑ j ∈ J, v j) / 32 ≤
      (marksRowMeasure (n + 1)).real (forcedRowsEvent u J v q t b) := by
  have hpow : (Finset.univ \ insert u J).card ≤ n := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_insert_of_notMem hu]
    omega
  have hx : (0 : ℝ) ≤ 1 - 1 / n := by
    rw [← htb]
    exact sub_nonneg.mpr ((mul_le_of_le_one_left hb.1 ht.2).trans hb.2)
  have hx' : (1 : ℝ) - 1 / n ≤ 1 := sub_le_self _ (by positivity)
  have hquiet : (1 / 4 : ℝ) ≤ (marksRowMeasure (n + 1)).real (noGood u J t b) := by
    rw [measureReal_noGood u J ht hb, htb]
    exact (quarter_le_pow_one_sub_inv hn).trans (pow_le_pow_of_le_one hx hx' hpow)
  have htight := measureReal_tight_lower hu hq ht hv hsmall
  rw [measureReal_forcedRowsEvent]
  have hnonneg : 0 ≤ t * (1 + ∑ j ∈ J, v j) / 8 := by
    have hsum : 0 ≤ ∑ j ∈ J, v j := Finset.sum_nonneg fun j hj ↦ (hv j hj).1
    exact div_nonneg (mul_nonneg ht.1 (by linarith)) (by norm_num)
  nlinarith only [mul_le_mul htight hquiet (by norm_num) (by positivity), hnonneg]

end WorkerCompromiseProof.Bounds
