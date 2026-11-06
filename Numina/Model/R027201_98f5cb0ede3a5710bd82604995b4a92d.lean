import Mathlib

theorem algebra_14320 (x : ℝ) :
    6*x^4 - 35*x^3 + 62*x^2 - 35*x + 6 = 0 ↔
    x = 2 ∨ x = 3 ∨ x = 1/2 ∨ x = 1/3 := by
  constructor
  · -- Forward direction: If the polynomial equals zero, prove the roots.
    intro h
    have h1 : (x - 2) * (x - 3) * (2 * x - 1) * (3 * x - 1) = 0 := by 
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3), sq_nonneg (x - 1/2), sq_nonneg (x - 1/3)]
    cases' (mul_eq_zero.mp h1) with h2 h1
    cases' (mul_eq_zero.mp h2) with h2 h1
    cases' (mul_eq_zero.mp h2) with h2 h1
    · -- Case where x - 2 = 0, so x = 2
      left
      linarith
    · -- Case where x - 3 = 0, so x = 3
      right
      left
      linarith
    · -- Case where 2 * x - 1 = 0, so x = 1/2
      right
      right
      left
      linarith
    · -- Case where 3 * x - 1 = 0, so x = 1/3
      right
      right
      right
      linarith
  · -- Backward: If the roots are given, the polynomial equals zero.
    rintro (h | h | h | h)
    · -- Case x = 2
      rw [h]
      norm_num
    · -- Case x = 3
      rw [h]
      norm_num
    · -- Case x = 1/2
      rw [h]
      norm_num
    · -- Case x = 1/3
      rw [h]
      norm_num