import Mathlib

theorem number_theory_186537 (a b c : ℤ) (h : a = b + c) :
    ∃ x, a^4 + b^4 + c^4 = 2 * x^2 := by
  use (b^2 + b * c + c^2)
  rw [h]
  nlinarith [sq_nonneg (b + c - c), sq_nonneg (b + c - b), sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (b^2 + b * c + c^2)]