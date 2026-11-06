import Mathlib

theorem algebra_235978 (x y : ℝ) :
    x^3 + x + y + 1 ≠ 0 ∨ y * x^2 + x + y ≠ 0 ∨ y^2 + y - x^2 + 1 ≠ 0 := by
  by_contra h
  push_neg at h
  rcases h with ⟨h1, h2, h3⟩
  have eq1 : x ^ 3 + x + y + 1 = 0 := by linarith
  have eq2 : y * x ^ 2 + x + y = 0 := by linarith
  have eq3 : y ^ 2 + y - x ^ 2 + 1 = 0 := by linarith
  have h4 : (x + 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (x ^ 2 + 1), sq_nonneg (y + x), sq_nonneg (y - x), sq_nonneg (y * (y + 1)), sq_nonneg ((x) * (x + 1)), sq_nonneg ((y) * x), sq_nonneg ((y + 1) * x), mul_pos (show (0 : ℝ) < 2 by norm_num) (show (0 : ℝ) < 2 by norm_num)]
  have h5 : x + 1 = 0 := by
    apply pow_eq_zero 
    exact h4
  have h6 : x = -1 := by linarith
  have hy1 : y = 1 := by
    rw [h6] at h1
    nlinarith
  rw [h6, hy1] at h2
  nlinarith