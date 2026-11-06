import Mathlib

theorem inequalities_258428 (a b : ℕ) (_ : 0 < a) (h₀ : 0 < b) :
    a + b ≤ 1 + a * b := by 
  nlinarith [sq_nonneg (a - 1 : ℕ), sq_nonneg (b - 1 : ℕ), sq_nonneg (a : ℕ), sq_nonneg (b : ℕ), 
    mul_pos (show 0 < a by linarith) (show 0 < b by linarith), 
    mul_nonneg (show 0 ≤ a by nlinarith) (show 0 ≤ b by nlinarith)
    ]