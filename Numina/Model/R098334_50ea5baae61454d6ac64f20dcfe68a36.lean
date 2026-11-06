import Mathlib

theorem algebra_160486 (x : ℝ) :
    (101 * x ^ 2 - 18 * x + 1) ^ 2 - 121 * x ^ 2 * (101 * x ^ 2 - 18 * x + 1) +
    2020 * x ^ 4 = 0 ↔ x = 1 / 9 ∨ x = 1 / 18 := by
  constructor
  · -- Assume the equation is 0, prove x is either 1/9 or 1/18
    intro h
    have h1 : (101 * x ^ 2 - 18 * x + 1) ^ 2 - 121 * x ^ 2 * (101 * x ^ 2 - 18 * x + 1) + 2020 * x ^ 4 = 0 := by linarith
    have h2 : (-18 * x + 1) * (81 * x ^ 2 - 18 * x + 1) = 0 := by
      nlinarith [sq_nonneg (101 * x ^ 2 - 18 * x + 1 - 101 * x ^ 2), sq_nonneg (101 * x ^ 2 - 18 * x + 1 - 20 * x ^ 2)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case $-18x + 1 = 0$
      right
      linarith
    · -- Case $81x^2 - 18x + 1 = 0$
      have h5 : 81 * x ^ 2 - 18 * x + 1 = 0 := by linarith
      have h6 : (9 * x - 1) ^ 2 = 0 := by nlinarith
      have h7 : 9 * x - 1 = 0 := by
        apply pow_eq_zero 
        exact h6
      left
      linarith
  · -- Assume x = 1/9 or x = 1/18, prove the equation is 0
    rintro (h | h)
    · -- Case x = 1/9
      rw [h]
      norm_num
    · -- Case x = 1/18
      rw [h]
      norm_num