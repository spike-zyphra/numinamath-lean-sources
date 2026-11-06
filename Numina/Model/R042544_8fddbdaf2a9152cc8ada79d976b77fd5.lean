import Mathlib

theorem algebra_234258 (x : ℝ) :
    (x^2 + 2 * x^3) = 3 * x^4 ↔ x = 1 ∨ x = -1 / 3 ∨ x = 0 := by
  constructor
  · -- Assume (x^2 + 2 * x^3) = 3 * x^4, prove x = 1 ∨ x = -1 / 3 ∨ x = 0
    intro h
    have h1 : 3 * x^4 - 2 * x^3 - x^2 = 0 := by
      nlinarith
    have h2 : x^2 * (3 * x^2 - 2 * x - 1) = 0 := by
      nlinarith [h1]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case where x^2 = 0, so x = 0
      have h5 : x = 0 := by
        nlinarith
      right
      right
      exact h5
    · -- Case where 3 * x^2 - 2 * x - 1 = 0
      have h5 : 3 * x^2 - 2 * x - 1 = 0 := h4
      have h6 : (x - 1) * (3 * x + 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h6) with h7 h8
      · -- Case where x - 1 = 0, so x = 1
        left
        linarith
      · -- Case where 3 * x + 1 = 0, so x = -1/3
        right
        left
        linarith
  · -- Assume x = 1 ∨ x = -1 / 3 ∨ x = 0, prove (x^2 + 2 * x^3) = 3 * x^4
    rintro (h | h | h)
    · -- Case x = 1
      rw [h]
      norm_num
    · -- Case x = -1/3
      rw [h]
      norm_num
    · -- Case x = 0
      rw [h]
      norm_num