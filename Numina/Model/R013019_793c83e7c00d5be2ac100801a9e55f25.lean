import Mathlib

theorem algebra_148024 (x : ℝ) :
    (Real.sin x + 2 * Real.cos x)^2 + (2 * Real.sin x - Real.cos x)^2 = 5 := by
  have h1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have eq2 : (Real.sin x + 2 * Real.cos x) ^ 2 + (2 * Real.sin x - Real.cos x) ^ 2 = 5 * (Real.sin x ^ 2 + Real.cos x ^ 2) := by
    ring
  rw [eq2, h1]
  all_goals norm_num