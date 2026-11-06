import Mathlib

theorem algebra_3187 {x y : ℝ} (h : x ^ 2 + 2 * y ^ 2 = 0) : x ^ 2 + y ^ 2 = 0 := by
  have h₁ : x ^ 2 ≥ 0 := sq_nonneg x
  have h₂ : y ^ 2 ≥ 0 := sq_nonneg y
  have h₃ : x ^ 2 = 0 := by
    nlinarith [sq_nonneg y]
  have h₄ : y ^ 2 = 0 := by 
    nlinarith [h₃, sq_nonneg x]
  linarith [h₃, h₄]