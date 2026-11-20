/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WorkerCompromiseProof.Branch
public import WorkerCompromiseProof.Child
public import WorkerCompromiseProof.Numbers
public import WorkerCompromiseProof.Choices
public import WorkerCompromiseProof.Screen
public import WorkerCompromiseProof.Union

/-!
# Backward induction over fixed partial assignments

Keep the recorded rows at arbitrary values and draw the others from their original product law.
A bad completion either has too few forced rows or witnesses one of the labeled extensions.
Each extension reveals only its own rows before invoking the next-stage bound.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open MeasureTheory
open scoped Classical ENNReal

private theorem measure_stopped {n : ℕ} {u : Fin (n+1)} (P : Partial n u)
    (z : MarksProfile n (n+1)) {q cutoff stop : ℝ}
    (hmark : ∀ i ∈ P.rows, cutoff ≤ (z i (P.assignment i)).2.val) (hD : stop ≤ P.mass z) :
    marksProfileMeasure n (n+1) ((freezeRows P.rows z) ⁻¹' badCompletion P q cutoff stop) = 0 := by
  have hempty : (freezeRows P.rows z) ⁻¹' badCompletion P q cutoff stop = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x
    exact not_badCompletion_of_mass P z (fun i hi ↦ by simp [freezeRows, hi]) hmark hD
  rw [hempty, measure_empty]

private theorem one_stage {n : ℕ} {u : Fin (n+1)} (P : Partial n u)
    (z : MarksProfile n (n+1)) {q cutoff stop b : ℝ}
    (hn : 2 ≤ n) (hq : q ∈ Set.Icc (1/2 : ℝ) 1) (hb : 0 < b)
    (hb1 : b ≤ 1) (hnb : 1 ≤ (n : ℝ)*b) (hcap : stop/b ≤ (n : ℝ)/2)
    (hinv : 1024 ≤ b⁻¹) (hlive : P.mass z < stop)
    (hmark : ∀ i ∈ P.rows, b ≤ (z i (P.assignment i)).2.val)
    (hchild : ∀ (F : Label n) (hF : P.Valid F) (x : MarksProfile n (n+1)),
      freezeRows P.rows z x ∈ retained P z F q (1/((n:ℝ)*b)) b hF →
      marksProfileMeasure n (n+1)
        ((freezeRows (P.extend F hF).rows (freezeRows P.rows z x)) ⁻¹'
          badCompletion (P.extend F hF) q cutoff stop) ≤
      ENNReal.ofReal (Real.exp (-((P.extend F hF).mass (freezeRows P.rows z x)) /
        (1024*(b/8192))))) :
    marksProfileMeasure n (n+1) ((freezeRows P.rows z) ⁻¹' badCompletion P q cutoff stop) ≤
      ENNReal.ofReal (Real.exp (-P.mass z/(1024*b))) := by
  let μ := marksProfileMeasure n (n+1)
  let I := Finset.univ \ P.rows
  let t := 1/((n:ℝ)*b)
  let G := forcedRowsEvent u P.workers (P.lower z) q t b
  let S := {x : MarksProfile n (n+1) | ((I.filter (fun i ↦ x i ∈ G)).card : ℝ) <
    P.mass z/(128*b)}
  let W := choiceWeight P z q t b
  let A (F : Label n) (hF : P.Valid F) := (freezeRows P.rows z) ⁻¹'
    (retained P z F q t b hF ∩ badCompletion (P.extend F hF) q cutoff stop)
  let w (F : Label n) := ∫⁻ x, ∏ i, (F i).elim 1 (fun j ↦ W i j (x i)) ∂μ
  let a := ENNReal.ofReal (Real.exp (-8*P.mass z/b))
  let c := ENNReal.ofReal (t^2 * P.mass z * b / 8)
  have hcov (x) (hx : x ∈ (freezeRows P.rows z) ⁻¹' badCompletion P q cutoff stop) :
      x ∈ S ∨ ∃ F hF, x ∈ A F hF := by
    have hagree (i) (hi : i ∈ P.rows) : freezeRows P.rows z x i = z i := by
      simp [freezeRows, hi]
    rcases badCompletion_cover P z (by linarith [hq.1]) hb hagree hx with h | ⟨F,hF,hA,hB⟩
    · left
      have hfilter : I.filter (fun i ↦ freezeRows P.rows z x i ∈ G) =
          I.filter (fun i ↦ x i ∈ G) := by
        apply Finset.filter_congr
        intro i hi
        have hnot := (Finset.mem_sdiff.mp hi).2
        simp [freezeRows, hnot]
      change ((I.filter (fun i ↦ freezeRows P.rows z x i ∈ G)).card : ℝ) < _ at h
      change ((I.filter (fun i ↦ x i ∈ G)).card : ℝ) < _
      rwa [hfilter] at h
    · exact Or.inr ⟨F,hF,hA,hB⟩
  have hbranch (F) (hF : P.Valid F) : μ (A F hF) ≤ a * w F :=
    measure_branch_le P z F q t b cutoff stop hF (hchild F hF)
  have hu := measure_guarded_cover_le μ ((freezeRows P.rows z) ⁻¹' badCompletion P q cutoff stop)
    S P.Valid A (fun F ↦ a*w F) hcov hbranch
  obtain ⟨hcard,hsmall,hscale⟩ := paper_screen_inputs P z hb hmark hlive hcap hinv
  have hscreen : μ S ≤ ENNReal.ofReal (Real.exp (-P.mass z/(512*b))) :=
    measure_forcedRows_few_le I u P.workers (P.lower z) q b (P.mass z)
      hn P.vacancy_fresh hq hb hb1 hnb (fun _ hj ↦ P.lower_mem z hj)
      (P.mass_eq z) hsmall hcard
  have ht : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by dsimp [t]; positivity, (div_le_one (by positivity)).mpr hnb⟩
  have hweights : ∑ F, w F ≤ (1 + n*c)^n :=
    sum_integral_choices_le W c (fun i j ↦ measurable_choiceWeight P z q t b i j)
      (fun i j ↦ lintegral_choiceWeight_le P z i j ⟨by linarith [hq.1],hq.2⟩ ht hb)
  rw [← Finset.mul_sum] at hu
  exact hu.trans ((add_le_add hscreen (mul_le_mul_of_nonneg_left hweights bot_le)).trans
    (paper_step_weight_ennreal_le (by omega : 0 < n) hb hscale))

/-- For every fixed partial assignment and every value of its recorded rows, the probability
that some stable completion misses the worker tail bound is exponentially small. -/
theorem measure_badCompletion_le {n L : ℕ} (b : ℕ → ℝ) {q stop cutoff : ℝ}
    (hn : 2 ≤ n) (hq : q ∈ Set.Icc (1/2 : ℝ) 1) (hstop : stop ≤ (129/128:ℝ)^L)
    (hb : ∀ l ≤ L, 0 < b l) (hnext : ∀ l < L, b (l+1) = b l / 8192)
    (hcut : ∀ l ≤ L, cutoff ≤ b l)
    (hnum : ∀ l < L, b l ≤ 1 ∧ 1 ≤ (n : ℝ)*b l ∧
      stop / b l ≤ (n : ℝ)/2 ∧ 1024 ≤ (b l)⁻¹)
    {l : ℕ} (hl : l ≤ L) {u : Fin (n+1)} (P : Partial n u) (z : MarksProfile n (n+1))
    (hm : ∀ i ∈ P.rows, b l ≤ (z i (P.assignment i)).2.val)
    (hg : (129/128:ℝ)^l ≤ P.mass z) :
    marksProfileMeasure n (n+1) ((freezeRows P.rows z) ⁻¹' badCompletion P q cutoff stop) ≤
      ENNReal.ofReal (Real.exp (-P.mass z/(1024*b l))) := by
  revert P z
  induction hl using Nat.decreasingInduction with
  | self =>
    intro P z hm hg
    rw [measure_stopped P z (fun i hi ↦ (hcut L le_rfl).trans (hm i hi)) (hstop.trans hg)]
    exact bot_le
  | of_succ l hl ih =>
    intro P z hm hg
    by_cases live : P.mass z < stop
    · obtain ⟨hb1,hnb,hcap,hinv⟩ := hnum l hl
      apply one_stage P z hn hq (hb l hl.le) hb1 hnb hcap hinv live hm
      intro F hF x hx
      have hagree (i) (hi : i ∈ P.rows) : freezeRows P.rows z x i = z i := by
        simp [freezeRows, hi]
      have hm' := retained_child_marks P z F hF (hb l hl.le).le hagree hm hx
      have hg' := retained_child_growth P z F hF hx
      have hnew : (129/128:ℝ)^(l+1) ≤ (P.extend F hF).mass (freezeRows P.rows z x) := by
        rw [pow_succ']
        exact (mul_le_mul_of_nonneg_left hg (by norm_num)).trans hg'
      simpa only [hnext l hl] using
        ih (P.extend F hF) (freezeRows P.rows z x) (by simpa only [hnext l hl] using hm') hnew
    · rw [measure_stopped P z (fun i hi ↦ (hcut l hl.le).trans (hm i hi)) (le_of_not_gt live)]
      exact bot_le

end WorkerCompromiseProof.Bounds.Paper
