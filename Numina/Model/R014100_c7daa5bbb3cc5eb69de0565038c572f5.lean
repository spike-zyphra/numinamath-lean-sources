import Mathlib

theorem algebra_12615 (x : ℝ) :
    6 * x ^ 4 + 19 * x ^ 3 - 51 * x ^ 2 + 20 * x = 0 ↔
    x = 0 ∨ x = 1 / 2 ∨ x = 4 / 3 ∨ x = -5 := by 
  constructor
  · -- Assume the polynomial equals zero, prove the disjunction of roots
    intro h
    have h1 : x * (3 * x - 4) * (2 * x - 1) * (x + 5) = 0 := by
      nlinarith [sq_nonneg (x * (3 * x - 4) * (2 * x - 1) * (x + 5)), sq_nonneg (x ^ 2), sq_nonneg ((2 * x) ^ 2), sq_nonneg ((3 * x ^ 2)), sq_nonneg ((x + 5) ^ 2)]
    cases' (mul_eq_zero.mp h1) with h2 h3
    · cases' (mul_eq_zero.mp h2) with h4 h5
      · cases' (mul_eq_zero.mp h4) with h6 h7
        · -- Case where x = 0
          left
          linarith
        · -- Case where 3 * x - 4 = 0, so x = 4 / 3
          right
          right
          left
          linarith
      · -- Case where 2 * x - 1 = 0, so x = 1 / 2
        right
        left
        linarith
    · -- Case where x + 5 = 0, so x = -5
      right
      right
      right
      linarith
  · -- Assume x is a root, prove the polynomial equals zero
    rintro (h | h | h | h)
    · -- Case x = 0
      rw [h]
      norm_num
    · -- Case x = 1 / 2
      rw [h]
      norm_num
    · -- Case x = 4 / 3
      rw [h]
      norm_num
    · -- Case x = -5
      rw [h]
      norm_num