import Mathlib

theorem algebra_6069 (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 ≤ 1 := by 
  have h1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  linarith [h1]