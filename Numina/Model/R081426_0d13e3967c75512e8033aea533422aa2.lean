import Mathlib

theorem algebra_5685 (x : ℝ) (h : Real.tan x = 3) : Real.sin x ^ 2 = 9 / 10 := by
  have h1 : Real.cos x ≠ 0 := by
    by_contra h2 
    have h3 : Real.tan x = 0 := by 
      rw [Real.tan_eq_sin_div_cos]
      simp [h2]
    rw [h3] at h 
    linarith

  have h2 : Real.sin x = 3 * Real.cos x := by
    have htan : Real.tan x = Real.sin x / Real.cos x := by
      rw [Real.tan_eq_sin_div_cos]
    rw [htan] at h
    have : Real.sin x = 3 * Real.cos x := by
      field_simp [h1] at h ⊢
      linarith
    assumption

  have h3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x

  have h4 : Real.sin x ^ 2 = 9 * Real.cos x ^ 2 := by
    rw [h2]
    ring

  have h5 : Real.cos x ^ 2 = 1 / 10 := by
    nlinarith [h3, h4]

  rw [h4]
  nlinarith [h5]