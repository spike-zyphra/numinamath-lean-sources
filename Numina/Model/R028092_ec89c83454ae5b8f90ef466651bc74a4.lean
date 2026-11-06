import Mathlib

theorem algebra_316378 (a b c : ℝ) (h₀ : a + b + c = 1) (h₁ : a ^ 2 + b ^ 2 + c ^ 2 = 3) :
    a * b * c ≤ 5 / 27 := by 
  have h2 : a * b + a * c + b * c = -1 := by
    have eq1 : a + b + c = 1 := h₀
    have eq2 : a ^ 2 + b ^ 2 + c ^ 2 = 3 := h₁
    have eq3 : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + a * c + b * c) := by
      ring
    rw [show (a + b + c) ^ 2 = (1 : ℝ) by nlinarith] at eq3
    rw [show a ^ 2 + b ^ 2 + c ^ 2 = (3 : ℝ) by linarith] at eq3
    linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a + b + c - 1), sq_nonneg (a ^ 2 + b ^ 2 + c ^ 2 - 3), 
          sq_nonneg (a * b + a * c + b * c + 1), 
          sq_nonneg (a - (-1/3)), sq_nonneg (b - 5/3), sq_nonneg (c - (-1/3))]