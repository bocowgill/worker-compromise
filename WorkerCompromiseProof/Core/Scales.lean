/-
Copyright 2026 The Market First Bridge Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib
public import WorkerCompromiseProof.Core.Model

/-!
# Induction scales and asymptotic estimates
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace WorkerCompromiseProof.Bounds

/-- The number of stages used for a market of size $n$. -/
noncomputable def stageCount (n : ℕ) : ℕ :=
  ⌊Real.log n / (8 * Real.log 8192)⌋₊

/-- The initial scale is $(\log n)^{-2}$ and the scale shrinks by $8192$ each stage. -/
noncomputable def stageScale (n l : ℕ) : ℝ :=
  ((Real.log n) ^ 2 * (8192 : ℝ) ^ l)⁻¹

/-- A history terminates when its accumulated weight reaches this polynomial target. -/
noncomputable def historyGrowthTarget (n : ℕ) : ℝ :=
  (n : ℝ) ^ (1 / 100000 : ℝ)

@[simp] theorem stageScale_zero (n : ℕ) : stageScale n 0 = ((Real.log n) ^ 2)⁻¹ := by
  simp [stageScale]

@[simp] theorem stageScale_succ (n l : ℕ) : stageScale n (l + 1) = stageScale n l / 8192 := by
  simp [stageScale, pow_succ, div_eq_mul_inv, mul_assoc, mul_comm]

theorem stageScale_pos {n : ℕ} (hn : 2 ≤ n) (l : ℕ) : 0 < stageScale n l := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast Nat.one_lt_two.trans_le hn)
  unfold stageScale
  positivity

theorem stageScale_le_root (n l : ℕ) : stageScale n l ≤ ((Real.log n) ^ 2)⁻¹ := by
  induction l with
  | zero => rw [stageScale_zero]
  | succ l ih =>
      rw [stageScale_succ]
      exact (div_le_self (by unfold stageScale; positivity) (by norm_num)).trans ih

private theorem log_base_bounds : 1 ≤ 8 * Real.log 8192 ∧ 8 * Real.log 8192 ≤ 104 := by
  have hlo := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) (by norm_num)
  have hhi := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
  have h : Real.log 8192 = 13 * Real.log 2 := by
    rw [show (8192 : ℝ) = (2 : ℝ) ^ (13 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [h]
  norm_num at hlo hhi
  constructor <;> linarith

private theorem log_tendsto : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem eventually_log_sq_le_rpow :
    ∀ᶠ n : ℕ in atTop, (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ (1 / 8 : ℝ) := by
  have ho := (isLittleO_log_rpow_atTop (r := (1 / 16 : ℝ)) (by norm_num)).def
    (c := (1 : ℝ)) (by norm_num)
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually ho] with n hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hpow : 0 ≤ (n : ℝ) ^ (1 / 16 : ℝ) := Real.rpow_nonneg (by positivity) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg hpow, one_mul] at hn
  calc
    _ ≤ ((n : ℝ) ^ (1 / 16 : ℝ)) ^ (2 : ℕ) := by gcongr
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num

private theorem base_pow_le {n l : ℕ} (hn : 2 ≤ n) (hl : l ≤ stageCount n) :
    (8192 : ℝ) ^ l ≤ (n : ℝ) ^ (1 / 8 : ℝ) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_two.trans_le hn)
  have hbase : 0 < Real.log 8192 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hl' : (l : ℝ) ≤ Real.log n / (8 * Real.log 8192) :=
    (Nat.cast_le.mpr hl).trans (Nat.floor_le (by positivity))
  calc
    _ = Real.exp ((l : ℝ) * Real.log 8192) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    _ ≤ Real.exp (Real.log n * (1 / 8)) := by
      apply Real.exp_le_exp.mpr
      have h := (le_div_iff₀ (by positivity : 0 < 8 * Real.log 8192)).mp hl'
      nlinarith
    _ = _ := (Real.rpow_def_of_pos hn' _).symm

/-- Every scheduled scale is at least the cutoff for the worker marks in the final tail. -/
theorem eventually_stageScale_ge_cutoff :
    ∀ᶠ n : ℕ in atTop, ∀ l ≤ stageCount n, (n : ℝ) ^ (-1 / 4 : ℝ) ≤ stageScale n l := by
  filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_log_sq_le_rpow] with n hn hs l hl
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_two.trans_le hn)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast Nat.one_lt_two.trans_le hn)
  have hd : (Real.log (n : ℝ)) ^ 2 * (8192 : ℝ) ^ l ≤ (n : ℝ) ^ (1 / 4 : ℝ) := calc
    _ ≤ (n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (1 / 8 : ℝ) :=
      mul_le_mul hs (base_pow_le hn hl) (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add hn']; norm_num
  unfold stageScale
  rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring, Real.rpow_neg hn'.le]
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hd

/-- The scales satisfy the bounds used in each finite probability estimate. -/
theorem eventually_stageScale_hypotheses :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ ∀ l ≤ stageCount n,
      0 < stageScale n l ∧ stageScale n l ≤ 1 ∧
      1 ≤ (n : ℝ) * stageScale n l ∧ (n : ℝ) ^ (-1 / 4 : ℝ) ≤ stageScale n l ∧
      historyGrowthTarget n / stageScale n l ≤ (n : ℝ) / 2 ∧
      512 ≤ (stageScale n l)⁻¹ := by
  have hp : Tendsto (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_stageScale_ge_cutoff, eventually_ge_atTop (2 : ℕ),
    log_tendsto.eventually_ge_atTop 32, (hp.comp hcast).eventually_ge_atTop 2]
      with n hcut hn hlog hp'
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast ((by omega : 1 ≤ n))
  have hn0 : 0 < (n : ℝ) := by positivity
  refine ⟨hn, fun l hl ↦ ?_⟩
  have hb := stageScale_pos hn l
  have hroot := stageScale_le_root n l
  have hcut' := hcut l hl
  have hs : 512 ≤ ((Real.log (n : ℝ)) ^ 2) := by nlinarith
  refine ⟨hb, hroot.trans ?_, ?_, hcut', ?_, ?_⟩
  · exact inv_le_one_of_one_le₀ (by linarith)
  · calc
      _ = (n : ℝ) ^ (0 : ℝ) := by simp
      _ ≤ (n : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn' (by norm_num)
      _ = (n : ℝ) * (n : ℝ) ^ (-1 / 4 : ℝ) := by
        calc
          _ = (n : ℝ) ^ (1 + (-1 / 4) : ℝ) := by norm_num
          _ = _ := by rw [Real.rpow_add hn0, Real.rpow_one]
      _ ≤ _ := by gcongr
  · have hx : historyGrowthTarget n / stageScale n l ≤ (n : ℝ) ^ (1 / 2 : ℝ) := calc
      _ ≤ historyGrowthTarget n / ((n : ℝ) ^ (-1 / 4 : ℝ)) := by
        gcongr
        exact Real.rpow_nonneg hn0.le _
      _ = (n : ℝ) ^ (1 / 100000 + 1 / 4 : ℝ) := by
        unfold historyGrowthTarget
        rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring, Real.rpow_neg hn0.le,
          div_inv_eq_mul, ← Real.rpow_add hn0]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn' (by norm_num)
    have hp'' : 2 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := hp'
    have hsq : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = (n : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      norm_num
    have : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) / 2 := by
      have h := mul_le_mul_of_nonneg_right hp'' (Real.rpow_nonneg hn0.le (1 / 2 : ℝ))
      nlinarith
    exact hx.trans this
  · have h := (inv_le_inv₀ (by positivity : 0 < ((Real.log (n : ℝ)) ^ 2)⁻¹) hb).mpr hroot
    simpa using hs.trans (by simpa using h)

private theorem log_growth_lower : (1 / 257 : ℝ) ≤ Real.log (1 + 1 / 256) := by
  have h := Real.one_sub_inv_le_log_of_pos (x := (1 + 1 / 256 : ℝ)) (by norm_num)
  norm_num at h ⊢
  exact h

/-- The accumulated multiplicative growth reaches the prescribed polynomial target. -/
theorem eventually_stageCount_growth :
    ∀ᶠ n : ℕ in atTop, historyGrowthTarget n ≤ (1 + 1 / 256 : ℝ) ^ stageCount n := by
  filter_upwards [eventually_ge_atTop (2 : ℕ), log_tendsto.eventually_ge_atTop 1000] with n hn hlog
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_two.trans_le hn)
  have hl : Real.log (n : ℝ) / 104 - 1 ≤ (stageCount n : ℝ) := by
    have hv := Nat.lt_floor_add_one (Real.log (n : ℝ) / (8 * Real.log 8192))
    change _ < (stageCount n : ℝ) + 1 at hv
    have hd : Real.log (n : ℝ) / 104 ≤ Real.log (n : ℝ) / (8 * Real.log 8192) := by
      have hbase : 0 < 8 * Real.log 8192 := zero_lt_one.trans_le log_base_bounds.1
      exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg n) hbase log_base_bounds.2
    linarith
  have hg : Real.log (n : ℝ) * (1 / 100000 : ℝ) ≤
      (stageCount n : ℝ) * Real.log (1 + 1 / 256) := by
    calc
      _ ≤ (Real.log (n : ℝ) / 104 - 1) * (1 / 257) := by linarith
      _ ≤ _ := mul_le_mul hl log_growth_lower (by norm_num) (by positivity)
  unfold historyGrowthTarget
  rw [Real.rpow_def_of_pos hn0]
  calc
    _ ≤ Real.exp ((stageCount n : ℝ) * Real.log (1 + 1 / 256)) := Real.exp_le_exp.mpr hg
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- A large firm score would allow a compromise in the one-extra-worker market. -/
noncomputable def firmScoreCutoff (n : ℕ) : ℝ :=
  (n : ℝ) ^ (1 / 2 - 1 / 200000 : ℝ)

/-- The smallest individual worker mark retained in the tail estimate. -/
noncomputable def workerMarkCutoff (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-1 / 4 : ℝ)

/-- The multiplicative mark threshold corresponding to the fixed switching cost. -/
noncomputable def compromiseQ (n : ℕ) : ℝ :=
  Real.exp (-switchingCost n)

private theorem eventually_log_le_mul_rpow {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ c * (n : ℝ) ^ r := by
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually ((isLittleO_log_rpow_atTop hr).def hc)] with n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg n),
    abs_of_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) r)] using hn

theorem compromiseQ_le_one (n : ℕ) : compromiseQ n ≤ 1 := by
  unfold compromiseQ switchingCost
  exact Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (div_nonneg (Real.log_natCast_nonneg n) (by positivity)))

/-- The mark threshold stays above one-half for all sufficiently large markets. -/
theorem eventually_compromiseQ_ge_half :
    ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ≤ compromiseQ n := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
      eventually_log_le_mul_rpow (c := 1) (r := 1 / 2) (by norm_num) (by norm_num)]
    with n hn hlog
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_two.trans_le hn)
  rw [one_mul, ← Real.sqrt_eq_rpow] at hlog
  have hcost : switchingCost n ≤ 1 / 2 := by
    unfold switchingCost
    apply (div_le_iff₀ (by positivity : 0 < 6 * Real.sqrt (n : ℝ))).mpr
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h ⊢
    exact h
  calc
    _ = Real.exp (-Real.log 2) := by rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]
    _ ≤ _ := Real.exp_le_exp.mpr (neg_le_neg (hcost.trans hlog2))

/-- The expected-count bound for a large firm score and a large worker tail. -/
noncomputable def annealedEnvelope (n : ℕ) : ℝ :=
  let q := compromiseQ n
  let s := firmScoreCutoff n
  let B := historyGrowthTarget n - 1
  let b := workerMarkCutoff n
  (n : ℝ) * ((n : ℝ) + 1) * Real.log ((n : ℝ) / s) *
    q ^ (-(2 * (n : ℝ))) * Real.exp (-(q ^ 2 * s * B) / 2) *
    (1 + 2 * Real.exp (-(q ^ 2 * s * b) / 2)) ^ n

private theorem switchingCost_mul (n : ℕ) (hn : 0 < (n : ℝ)) :
    2 * (n : ℝ) * switchingCost n = (n : ℝ) ^ (1 / 2 : ℝ) * (Real.log n / 3) := by
  rw [switchingCost, ← Real.sqrt_eq_rpow]
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hn).ne'
  have he : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hn.le
  field_simp [hs]
  rw [he]
  ring

private theorem exp_log_mul_neg_nat (x : ℝ) (hx : 0 < x) (k : ℕ) :
    Real.exp (Real.log x * -(k : ℝ)) = x⁻¹ ^ k := by
  rw [← Real.rpow_def_of_pos hx, Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]

/-- The worker tail penalty dominates both the switching-cost factor and the polynomial prefactor. -/
theorem tendsto_annealedEnvelope_zero :
    Tendsto annealedEnvelope atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun n : ℕ ↦ (2 * Real.exp 1) * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using hi.const_mul (2 * Real.exp 1)
  have hp : Tendsto historyGrowthTarget atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 / 100000 : ℝ))).comp
      tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 / 2 ≤ compromiseQ n ∧
      2 ≤ historyGrowthTarget n ∧
      Real.log n ≤ (1 / 128 : ℝ) * (n : ℝ) ^ (1 / 200000 : ℝ) ∧
      Real.log n ≤ (1 / 128 : ℝ) * (n : ℝ) ^ (1 / 2 + 1 / 200000 : ℝ) ∧
      Real.log n ≤ (1 / 16 : ℝ) * (n : ℝ) ^ (1 / 4 - 1 / 200000 : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_compromiseQ_ge_half,
      hp.eventually_ge_atTop 2,
      eventually_log_le_mul_rpow (c := 1 / 128) (r := 1 / 200000) (by norm_num) (by norm_num),
      eventually_log_le_mul_rpow (c := 1 / 128) (r := 1 / 2 + 1 / 200000)
        (by norm_num) (by norm_num),
      eventually_log_le_mul_rpow (c := 1 / 16) (r := 1 / 4 - 1 / 200000)
        (by norm_num) (by norm_num)] with n hn hq hh h1 h2 h3
    exact ⟨hn, hq, hh, h1, h2, h3⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
  · filter_upwards [hevent] with n hn
    obtain ⟨hn, hq, hh, -⟩ := hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hn0 : 0 < (n : ℝ) := zero_lt_one.trans_le hn1
    have hs : 0 < firmScoreCutoff n := Real.rpow_pos_of_pos hn0 _
    have hle : firmScoreCutoff n ≤ (n : ℝ) := by
      unfold firmScoreCutoff
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1 / 2 - 1 / 200000 : ℝ) ≤ 1)
    have hlog : 0 ≤ Real.log ((n : ℝ) / firmScoreCutoff n) :=
      Real.log_nonneg ((le_div_iff₀ hs).mpr (by simpa using hle))
    unfold annealedEnvelope
    positivity
  filter_upwards [hevent] with n hn
  obtain ⟨hn, hq, hh, hlog1, hlog2, hlog3⟩ := hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := zero_lt_one.trans_le hn1
  let q := compromiseQ n
  let s := firmScoreCutoff n
  let B := historyGrowthTarget n - 1
  let b := workerMarkCutoff n
  have hq2 : (1 / 4 : ℝ) ≤ q ^ 2 := by
    change (1 / 2 : ℝ) ≤ q at hq
    nlinarith
  have hq0 : 0 < q := by linarith
  have hs : 0 < s := Real.rpow_pos_of_pos hn0 _
  have hs1 : 1 ≤ s := by
    unfold s firmScoreCutoff
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (0 : ℝ) ≤ 1 / 2 - 1 / 200000)
  have hB : historyGrowthTarget n / 2 ≤ B := by dsimp [B]; linarith
  have hprod : s * historyGrowthTarget n = (n : ℝ) ^ (1 / 2 + 1 / 200000 : ℝ) := by
    unfold s firmScoreCutoff historyGrowthTarget
    rw [← Real.rpow_add hn0]
    norm_num
  have hprod' : s * b = (n : ℝ) ^ (1 / 4 - 1 / 200000 : ℝ) := by
    unfold s b firmScoreCutoff workerMarkCutoff
    rw [← Real.rpow_add hn0]
    norm_num
  have hpenalty : (n : ℝ) ^ (1 / 2 + 1 / 200000 : ℝ) / 16 ≤ q ^ 2 * s * B / 2 := calc
    _ = (1 / 4 : ℝ) * s * (historyGrowthTarget n / 2) / 2 := by rw [← hprod]; ring
    _ ≤ _ := by gcongr
  have hcost : 2 * (n : ℝ) * switchingCost n ≤ (n : ℝ) ^ (1 / 2 + 1 / 200000 : ℝ) / 32 := by
    rw [switchingCost_mul n hn0]
    calc
      _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) * ((1 / 128 : ℝ) * (n : ℝ) ^ (1 / 200000 : ℝ) / 3) := by
        gcongr
      _ = (n : ℝ) ^ (1 / 2 + 1 / 200000 : ℝ) / 384 := by
        rw [Real.rpow_add hn0]
        ring
      _ ≤ _ := by
        have h := Real.rpow_nonneg hn0.le (1 / 2 + 1 / 200000 : ℝ)
        linarith
  have hbig : q ^ (-(2 * (n : ℝ))) * Real.exp (-(q ^ 2 * s * B) / 2) ≤ ((n : ℝ)⁻¹) ^ (4 : ℕ) := by
    have hlogq : Real.log q = -switchingCost n := Real.log_exp _
    rw [Real.rpow_def_of_pos hq0, hlogq, ← Real.exp_add, ← exp_log_mul_neg_nat (n : ℝ) hn0 4]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsmall : Real.exp (-(q ^ 2 * s * b) / 2) ≤ ((n : ℝ)⁻¹) ^ (2 : ℕ) := by
    rw [← exp_log_mul_neg_nat (n : ℝ) hn0 2]
    apply Real.exp_le_exp.mpr
    have hz : (1 / 4 : ℝ) * (s * b) / 2 ≤ q ^ 2 * s * b / 2 := by
      rw [mul_assoc (q ^ 2)]
      gcongr
      rw [hprod']
      positivity
    rw [hprod'] at hz
    nlinarith
  have hsmall' : 2 * (n : ℝ) * Real.exp (-(q ^ 2 * s * b) / 2) ≤ 1 := calc
    _ ≤ 2 * (n : ℝ) * ((n : ℝ)⁻¹) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = 2 / (n : ℝ) := by field_simp
    _ ≤ _ := (div_le_iff₀ hn0).2 (by linarith)
  have hfactor : (1 + 2 * Real.exp (-(q ^ 2 * s * b) / 2)) ^ n ≤ Real.exp 1 := calc
    _ ≤ (Real.exp (2 * Real.exp (-(q ^ 2 * s * b) / 2))) ^ n := by
      gcongr
      simpa only [add_comm] using Real.add_one_le_exp (2 * Real.exp (-(q ^ 2 * s * b) / 2))
    _ = Real.exp (2 * (n : ℝ) * Real.exp (-(q ^ 2 * s * b) / 2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hsmall'
  have hlogUp : Real.log ((n : ℝ) / s) ≤ (n : ℝ) :=
    ((Real.log_le_log (div_pos hn0 hs)) (div_le_self hn0.le hs1)).trans
      ((Real.log_le_sub_one_of_pos hn0).trans (by linarith))
  have hlog0 : 0 ≤ Real.log ((n : ℝ) / s) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hs).mpr
    unfold s firmScoreCutoff
    simpa only [one_mul, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1 / 2 - 1 / 200000 : ℝ) ≤ 1)
  calc
    annealedEnvelope n =
        ((n : ℝ) * ((n : ℝ) + 1) * Real.log ((n : ℝ) / s)) *
        (q ^ (-(2 * (n : ℝ))) * Real.exp (-(q ^ 2 * s * B) / 2)) *
        (1 + 2 * Real.exp (-(q ^ 2 * s * b) / 2)) ^ n := by unfold annealedEnvelope; ring
    _ ≤ ((n : ℝ) * (2 * (n : ℝ)) * (n : ℝ)) * ((n : ℝ)⁻¹) ^ (4 : ℕ) *
        Real.exp 1 := by
      gcongr
      linarith
    _ = _ := by field_simp

end WorkerCompromiseProof.Bounds
