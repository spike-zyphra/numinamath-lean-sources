import Mathlib

theorem algebra_20383 (x : ℤ) :
    x^4 + 5 * x^3 + 9 * x^2 - x - 14 = 0 ↔ x = -2 ∨ x = 1 := by
  constructor
  · -- Suppose x^4 + 5 * x^3 + 9 * x^2 - x - 14 = 0, prove x = -2 or x = 1
    intro h
    have h1 : x^4 + 5 * x^3 + 9 * x^2 - x - 14 = (x - 1) * (x + 2) * (x^2 + 4*x + 7) := by ring
    rw [h1] at h
    cases' (mul_eq_zero.mp h) with h2 h3
    cases' (mul_eq_zero.mp h2) with h4 h5
    · -- Case where x - 1 = 0
      right
      exact eq_of_sub_eq_zero h4
    · -- Case where x + 2 = 0
      left
      linarith
    · -- Case where x^2 + 4*x + 7 = 0, show contradiction (no integer solutions)
      have : x^2 + 4 * x + 7 > 0 := by
        nlinarith [sq_nonneg (x + 2)]
      nlinarith
  · -- Suppose x = -2 or x = 1, prove x^4 + 5 * x^3 + 9 * x^2 - x - 14 = 0
    rintro (h | h)
    · -- Case where x = -2
      rw [h]
      norm_num
    · -- Case where x = 1
      rw [h]
      norm_num