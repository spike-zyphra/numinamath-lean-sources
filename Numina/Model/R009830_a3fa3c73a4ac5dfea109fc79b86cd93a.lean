import Mathlib


theorem algebra_9199 (x : ℝ) :
    x ^ 2 = 4 * x ↔ x = 0 ∨ x = 4 := by
  constructor
  · -- Assume x^2 = 4 * x
    intro h
    have h1 : x ^ 2 - 4 * x = 0 := by linarith
    have h2 : x * (x - 4) = 0 := by 
      linarith [h1]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · left
      exact h3
    · right
      linarith
  · -- Assume x = 0 ∨ x = 4
    rintro (h | h)
    · -- If x = 0, prove x ^ 2 = 4 * x
      rw [h]
      norm_num
    · -- If x = 4, prove x ^ 2 = 4 * x
      rw [h]
      norm_num