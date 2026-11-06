import Mathlib

theorem algebra_226775 (x : ℝ) (h : Real.cos x + Real.sin x = 0.3) :
    Real.cos x ^ 3 + Real.sin x ^ 3 = 0.4365 := by
  have h1 : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
  have h2 : Real.cos x * Real.sin x = -0.455 := by
    have eq1 : (Real.cos x + Real.sin x) ^ 2 = Real.cos x ^ 2 + Real.sin x ^ 2 + 2 * (Real.cos x * Real.sin x) := by ring
    rw [h, h1] at eq1 -- substitute the value 0.3 and the identity 1
    norm_num at eq1
    linarith

  have eq3 : Real.cos x ^ 3 + Real.sin x ^ 3 = (Real.cos x + Real.sin x) ^ 3 - 3 * (Real.cos x * Real.sin x) * (Real.cos x + Real.sin x) := by
    ring

  rw [eq3, h, h2]
  norm_num