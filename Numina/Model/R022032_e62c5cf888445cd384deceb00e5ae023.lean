import Mathlib

theorem algebra_250237 (x : ℝ) (h : Real.cos x + Real.cos x ^ 2 + Real.cos x ^ 3 = 1) :
    (Real.sin x) ^ 6 - 4 * (Real.sin x) ^ 4 + 8 * (Real.sin x) ^ 2 = 4 := by
  have h1 : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
    have h2 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    linarith 
  have h2 : Real.sin x ^ 4 = (1 - Real.cos x ^ 2) ^ 2 := by 
    calc 
      Real.sin x ^ 4 = (Real.sin x ^ 2) ^ 2 := by ring
      _ = (1 - Real.cos x ^ 2) ^ 2 := by rw [h1]
  have h3 : Real.sin x ^ 6 = (1 - Real.cos x ^ 2) ^ 3 := by 
    calc 
      Real.sin x ^ 6 = (Real.sin x ^ 2) ^ 3 := by ring 
      _ = (1 - Real.cos x ^ 2) ^ 3 := by rw [h1]
  have eq1 : (Real.sin x) ^ 6 - 4 * (Real.sin x) ^ 4 + 8 * (Real.sin x) ^ 2 = 
    (1 - Real.cos x ^ 2) ^ 3 - 4 * (1 - Real.cos x ^ 2) ^ 2 + 8 * (1 - Real.cos x ^ 2) := by
    rw [h3, h2, h1]
  rw [eq1]
  nlinarith [sq_nonneg (Real.cos x ^ 2 - 1), sq_nonneg (Real.cos x - 0), sq_nonneg (Real.sin x ^ 2 - 0), Real.sin_sq_add_cos_sq x, sq_nonneg (Real.cos x + 1), sq_nonneg (Real.cos x ^ 2 - Real.cos x), sq_nonneg (Real.cos x ^ 2 - 1)]