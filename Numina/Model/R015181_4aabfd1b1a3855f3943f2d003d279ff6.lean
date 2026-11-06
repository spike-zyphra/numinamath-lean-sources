import Mathlib

theorem algebra_198459 (x : ℤ) : x * (x + 1) * (x + 2) * (x + 3) = 5040 ↔ x = -10 ∨ x = 7 := by
  constructor
  · -- Assume the equation holds, proving the possible values of x
    intro h
    have h1 : x * (x + 1) * (x + 2) * (x + 3) = 5040 := h
    have h2 : (x ^ 2 + 3 * x) * (x ^ 2 + 3 * x + 2) = 5040 := by
      ring_nf at h1 ⊢
      nlinarith
    have h5 : (x ^ 2 + 3 * x - 70) * (x ^ 2 + 3 * x + 72) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case where x^2 + 3 * x - 70 = 0
      have h8 : x ^ 2 + 3 * x = 70 := by
        nlinarith
      have h9 : (x - 7) * (x + 10) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h9) with h10 h11
      · -- Case where x - 7 = 0
        right
        linarith
      · -- Case where x + 10 = 0
        left
        linarith
    · -- Case where x ^ 2 + 3 * x + 72 = 0
      exfalso
      nlinarith [sq_nonneg (x + 1)]
  · -- Now the reverse direction: given the values satisfy the equation
    rintro (h | h)
    · -- Case where x = -10
      rw [h]
      norm_num
    · -- Case where x = 7
      rw [h]
      norm_num