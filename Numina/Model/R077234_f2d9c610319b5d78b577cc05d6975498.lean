import Mathlib

theorem algebra_5361 (x : ℝ) (hx : Real.tan x = 4) (h : Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2) :
    Real.sin (2 * x) = 8 / 17 := by
  have h1 : Real.cos x ≠ 0 := by
    by_contra h2
    have htan : Real.tan x = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h2]
    rw [htan] at hx
    norm_num at hx
  have h2 : Real.sin x = 4 * Real.cos x := by
    have htan : Real.tan x = Real.sin x / Real.cos x := by
      rw [Real.tan_eq_sin_div_cos]
    rw [htan] at hx
    have : Real.sin x = 4 * Real.cos x := by
      field_simp [h1] at hx
      linarith
    assumption
  have h3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h4 : Real.cos x ^ 2 = 1 / 17 := by
    rw [h2] at h3
    nlinarith [h3]
  have h6 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
    rw [Real.sin_two_mul]
  rw [h6, h2]
  nlinarith [h4]