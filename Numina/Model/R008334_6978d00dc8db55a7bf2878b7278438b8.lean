import Mathlib

theorem algebra_167673 (x : ℝ) (h : Real.sin x + Real.cos x = 1 / 2) :
    Real.sin x ^ 3 + Real.cos x ^ 3 = 11 / 16 := by 
  have h1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h2 : Real.sin x * Real.cos x = -3 / 8 := by 
    have h_sq : (Real.sin x + Real.cos x) ^ 2 = (1 / 2) ^ 2 := by rw [h]
    have eq1 : (Real.sin x + Real.cos x) ^ 2 = Real.sin x ^ 2 + Real.cos x ^ 2 + 2 * (Real.sin x * Real.cos x) := by ring
    rw [eq1] at h_sq
    rw [h1] at h_sq
    nlinarith
  have h3 : Real.sin x ^ 3 + Real.cos x ^ 3 = (Real.sin x + Real.cos x) ^ 3 - 3 * (Real.sin x + Real.cos x) * (Real.sin x * Real.cos x) := by
    ring
  rw [h3, h, h2]
  norm_num