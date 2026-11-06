import Mathlib

theorem algebra_2556 (x y : ℝ) (h : (x - 1996) ^ 2 + (7 + y) ^ 2 = 0) : x + y ^ 3 = 1653 := by
  have h₁ : (x - 1996) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h₂ : (7 + y) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h₃ : (x - 1996) ^ 2 = 0 := by 
    linarith
  have h₄ : (7 + y) ^ 2 = 0 := by 
    linarith
  have hx : x = 1996 := by
    nlinarith
  have hy : y = -7 := by
    nlinarith
  rw [hx, hy]
  norm_num