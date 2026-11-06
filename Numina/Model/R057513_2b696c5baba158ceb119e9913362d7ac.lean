import Mathlib

theorem algebra_143365 (x : ℝ) (h : Real.sin x - Real.cos x = 1 / 2) : Real.sin (2 * x) = 3 / 4 := by
  have h1 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
    rw [Real.sin_two_mul]

  have h2 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x

  have h3 : (Real.sin x - Real.cos x) ^ 2 = (1 / 2) ^ 2 := by
    rw [h]

  have h4 : Real.sin x ^ 2 + Real.cos x ^ 2 - 2 * (Real.sin x * Real.cos x) = 1 / 4 := by
    nlinarith [h3, Real.sin_sq_add_cos_sq x]

  have h5 : Real.sin x * Real.cos x = 3 / 8 := by
    have h6 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    linarith [h4, h6]

  rw [h1]
  linarith [h5]