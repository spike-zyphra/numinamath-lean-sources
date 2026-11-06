import Mathlib

theorem algebra_237892 (x : ℝ) : (x + 2)^4 + x^4 = 82 ↔ x = -3 ∨ x = 1 := by
  constructor
  · -- Assume (x + 2)^4 + x^4 = 82 prove x = -3 ∨ x = 1
    intro h_eq
    have h_eq2 : (x - 1) * (x + 3) * (x^2 + 2*x + 11) = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - x), sq_nonneg (x ^ 2 + x), sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x + 3), sq_nonneg (x^2 + 2*x + 11)]
    cases' (mul_eq_zero.mp h_eq2) with h_eq3 h_eq4
    cases' (mul_eq_zero.mp h_eq3) with h_eq5 h_eq6
    · -- Case where x - 1 = 0, so x = 1
      right
      linarith
    · -- Case where x + 3 = 0, so x = -3
      left
      linarith
    · -- Case where x^2 + 2x + 11 = 0, we need to show contradiction
      exfalso
      have h1 : x^2 + 2*x + 11 > 0 := by
        nlinarith [sq_nonneg (x + 1)]
      have h2 : x^2 + 2*x + 11 = 0 := by
        nlinarith
      linarith [h1, h2]
  · -- Assume x = -3 ∨ x = 1 prove (x + 2)^4 + x^4 = 82
    rintro (h | h)
    · -- Case x = -3
      rw [h]
      norm_num
    · -- Case x = 1
      rw [h]
      norm_num