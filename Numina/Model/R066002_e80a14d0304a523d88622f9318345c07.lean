import Mathlib

theorem algebra_296730 (x : ℝ) : x^2 - x + 1 = (x^2 + x + 1) * (x^2 + 2 * x + 4) ↔ x = -1 := by
  constructor
  · -- Forward implication: if the equation holds, then x = -1
    intro h
    have h1 : x^4 + 3 * x^3 + 6 * x^2 + 7 * x + 3 = 0 := by
      nlinarith [sq_nonneg (x^2 + x + 1), sq_nonneg (x^2 + 2 * x + 4)]
    have h2 : (x + 1)^2 * (x^2 + x + 3) = 0 := by
      nlinarith [h1]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case where (x + 1)^2 = 0
      have h5 : x + 1 = 0 := by 
        nlinarith
      linarith
    · -- Case where x^2 + x + 3 = 0
      have h5 : x^2 + x + 3 > 0 := by
        nlinarith [sq_nonneg (x + 1/2)]
      nlinarith
  · -- Reverse implication: if x = -1, then the equation holds
    intro h
    rw [h]
    norm_num