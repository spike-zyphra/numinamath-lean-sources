import Mathlib

theorem algebra_165561 (x : ℝ) : (x^2 + 2 * x)^2 - (x + 1)^2 = 55 ↔ x = -4 ∨ x = 2 := by
  constructor
  · -- Forward direction: If (x^2 + 2 * x)^2 - (x + 1)^2 = 55, then x = -4 ∨ x = 2
    rintro h
    have eq1 : (x^2 + 2 * x)^2 - (x + 1)^2 - 55 = 0 := by linarith
    have eq2 : (x - 2) * (x + 4) * (x^2 + 2 * x + 7) = 0 := by
      nlinarith [sq_nonneg (x^2 + 2 * x), sq_nonneg (x - 2), sq_nonneg (x + 4)]
    cases' (mul_eq_zero.mp eq2) with h3 h4
    cases' (mul_eq_zero.mp h3) with h5 h6
    · -- Case x - 2 = 0, so x = 2
      right
      linarith
    · -- Case x + 4 = 0, so x = -4
      left
      linarith
    · -- Case x^2 + 2x + 7 = 0, which has no real solutions
      have h7 : x^2 + 2 * x + 7 > 0 := by
        nlinarith [sq_nonneg (x + 1)]
      nlinarith
  · -- Backward direction: If x = -4 ∨ x = 2, then (x^2 + 2 * x)^2 - (x + 1)^2 = 55
    rintro (h | h)
    · -- Case x = -4
      rw [h]
      norm_num
    · -- Case x = 2
      rw [h]
      norm_num