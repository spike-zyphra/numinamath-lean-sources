import Mathlib

theorem algebra_108023 (x : ℝ) : x * (x + 1) * (x ^ 2 + x + 1) = 6 ↔ x = 1 ∨ x = -2 := by
  constructor
  · -- Assume the equation holds, prove the solutions.
    intro h
    have h1 : x * (x + 1) * (x ^ 2 + x + 1) = 6 := h
    have h2 : (x ^ 2 + x) * (x ^ 2 + x + 1) = 6 := by
      nlinarith [h1]
    have h3 : (x ^ 2 + x) ^ 2 + (x ^ 2 + x) - 6 = 0 := by
      nlinarith [h2]
    have h4 : (x ^ 2 + x - 2) * (x ^ 2 + x + 3) = 0 := by
      nlinarith [h3]
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case where $(x ^ 2 + x - 2) = 0$
      have h7 : x ^ 2 + x - 2 = 0 := by linarith
      have h8 : (x - 1) * (x + 2) = 0 := by
        nlinarith [h7]
      cases' (mul_eq_zero.mp h8) with h9 h10
      · -- Case where $x - 1 = 0$
        left
        linarith
      · -- Case where $x + 2 = 0$
        right
        linarith
    · -- Case where $(x ^ 2 + x + 3) = 0$
      have h8 : x ^ 2 + x + 3 = 0 := by linarith
      nlinarith [sq_nonneg (x + 0.5)]
  · -- Assume the solutions, prove the equation.
    rintro (h | h)
    · -- Case where x = 1
      rw [show x = 1 by linarith]
      norm_num
    · -- Case where x = -2
      rw [show x = -2 by linarith]
      norm_num