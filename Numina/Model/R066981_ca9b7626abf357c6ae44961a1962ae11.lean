import Mathlib

theorem algebra_22099 (x : ℤ) :
    2*x^3+13*x^2-23*x+8=0 ↔ x=-8 ∨ x=1 := by
  constructor
  · -- Assume the polynomial is zero, prove x = -8 ∨ x = 1
    intro h
    have h1 : (x - 1) * (x + 8) * (2 * x - 1) = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 8), sq_nonneg (2 * x - 1), h]
    cases' (mul_eq_zero.mp h1) with h2 h3
    · -- Case h2: either (x - 1) = 0 or (x + 8) = 0
      cases' (mul_eq_zero.mp h2) with h4 h5
      · -- Case h4
        right
        linarith
      · -- Case h5
        left
        linarith
    · -- Case h3: (2 * x - 1) = 0, which implies x = 1/2 which isn't integer, contradiction
      exfalso
      omega
  · -- Assume x = -8 ∨ x = 1, prove the polynomial is zero
    rintro (h | h)
    · -- Case x = -8
      rw [h]
      norm_num
    · -- Case x = 1
      rw [h]
      norm_num