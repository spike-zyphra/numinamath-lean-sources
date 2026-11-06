import Mathlib
open Real Set

theorem algebra_3148 (x : ℝ) (h₀ : sin x > 0) (h₁ : cos x = -0.8) :
    tan x = -0.75 := by
  have h2 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  rw [h₁] at h2
  have h4 : sin x ^ 2 = 1 - (-0.8 : ℝ) ^ 2 := by linarith
  have h5 : sin x ^ 2 = (0.36 : ℝ) := by
    rw [h4]
    norm_num
  have h6 : sin x = (0.6 : ℝ) := by
    nlinarith [h₀]
  have htan : tan x = sin x / cos x := by
    rw [Real.tan_eq_sin_div_cos]
  rw [htan, h6, h₁]
  norm_num