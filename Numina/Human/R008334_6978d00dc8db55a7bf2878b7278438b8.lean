import Mathlib

theorem algebra_167673 (x : ℝ) (h : Real.sin x + Real.cos x = 1 / 2) :
    Real.sin x ^ 3 + Real.cos x ^ 3 = 11 / 16 := by 
  have h1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h2 : Real.sin x * Real.cos x = -3 / 8 := by
    have h2 : (Real.sin x + Real.cos x) ^ 2 = 1 / 4 := by 
      rw [h]
      ring
    linarith [h1, h2, Real.sin_sq_add_cos_sq x]
  have h3 : Real.sin x ^ 3 + Real.cos x ^ 3 = (Real.sin x + Real.cos x) * ((Real.sin x ^ 2 + Real.cos x ^ 2) - Real.sin x * Real.cos x) := by
    ring
  rw [h3, h, h1, h2]
  norm_num