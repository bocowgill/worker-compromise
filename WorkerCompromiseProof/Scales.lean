module

public import WorkerCompromiseProof.Core.Scales

/-!
# Asymptotics for the paper's backward induction

The bound at the empty partial assignment is paid once per possible unmatched worker.
-/

@[expose] public section

namespace WorkerCompromiseProof.Bounds.Paper

open Filter
open scoped Topology

/-- On the paper's schedule the inverse scale eventually exceeds 1024 at every stage. -/
theorem eventually_inverse_stageScale :
    ∀ᶠ n : ℕ in atTop, ∀ l, 1024 ≤ (stageScale n l)⁻¹ := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlog.eventually_ge_atTop 32] with n hn h l
  have h₁ : 32 ≤ Real.log (n : ℝ) := h
  have h₂ : 1024 ≤ (Real.log (n : ℝ)) ^ 2 := by nlinarith [sq_nonneg (Real.log n - 32)]
  have hs := (inv_le_inv₀ (inv_pos.mpr (sq_pos_of_pos (by linarith : 0 < Real.log n)))
    (stageScale_pos hn l)).mpr (stageScale_le_root n l)
  exact h₂.trans (by simpa using hs)

/-- Summing the initial error over all vacancy labels still gives a vanishing probability. -/
theorem tendsto_vacancy_error :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) * Real.exp (-((Real.log n) ^ 2) / 1024))
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' (.of_forall fun _ ↦ by positivity)
    ?_ (by simpa using hinv.const_mul 2)
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlog.eventually_ge_atTop 2048] with n hn h
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn₀ : 0 < (n : ℝ) := by linarith
  have hlog' : 2048 ≤ Real.log (n : ℝ) := h
  have he : Real.exp (-((Real.log n) ^ 2) / 1024) ≤ ((n : ℝ)⁻¹) ^ 2 := calc
    _ ≤ Real.exp (Real.log (n : ℝ) * (-(2 : ℝ))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (by linarith : 0 ≤ Real.log n)
        (sub_nonneg.mpr hlog')]
    _ = (n : ℝ) ^ (-(2 : ℝ)) := (Real.rpow_def_of_pos hn₀ _).symm
    _ = _ := by rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_ofNat]
  calc
    _ ≤ (2 * (n : ℝ)) * ((n : ℝ)⁻¹) ^ 2 := mul_le_mul (by linarith) he (by positivity) (by positivity)
    _ = 2 * (n : ℝ)⁻¹ := by field_simp

end WorkerCompromiseProof.Bounds.Paper
