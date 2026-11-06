import Mathlib

theorem algebra_110577 (x : ℝ) :
    (x^2 + x + 1) * (3 - x - x^2) = 3 ↔ x = 0 ∨ x = -1 ∨ x = 1 ∨ x = -2 := by 
  constructor 
  · -- Assume the equation holds, prove the roots
    intro h
    have h1 : (x^2 + x + 1) * (3 - x - x^2) - 3 = 0 := by linarith
    have h2 : x * (x - 1) * (x + 1) * (x + 2) = 0 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 2), sq_nonneg (x), sq_nonneg (x - 2)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    cases' (mul_eq_zero.mp h3) with h5 h6
    cases' (mul_eq_zero.mp h5) with h7 h8
    · -- x = 0
      left
      linarith
    · -- x - 1 = 0
      right
      right
      left
      linarith
    · -- x + 1 = 0
      right
      left
      linarith
    · -- x + 2 = 0
      right
      right
      right
      linarith
  · -- Assume one of the roots, prove the equation
    rintro (h | h | h | h)
    · -- x = 0
      rw [h]
      norm_num
    · -- x = -1
      rw [h]
      norm_num
    · -- x = 1
      rw [h]
      norm_num
    · -- x = -2
      rw [h]
      norm_num