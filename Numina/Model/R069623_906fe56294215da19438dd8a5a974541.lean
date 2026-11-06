import Mathlib

theorem algebra_186717 (x : ℝ) : 8*x^4+x^3+64*x+8=0 ↔ x=-1/8 ∨ x=-2 := by
  constructor
  · -- First direction: if the polynomial is zero, prove x = -1/8 or x = -2
    intro h
    have h1 : 8 * x^4 + x^3 + 64 * x + 8 = (x + 2) * (x^2 - 2 * x + 4) * (8 * x + 1) := by
      ring
    rw [h1] at h
    cases' (mul_eq_zero.mp h) with h2 h3
    · -- Case where (x + 2) * (x^2 - 2 * x + 4) = 0
      cases' (mul_eq_zero.mp h2) with h4 h5
      · -- Case where x + 2 = 0, so x = -2
        have hx : x = -2 := by linarith
        right
        exact hx
      · -- Case where x^2 - 2x + 4 = 0
        have h6 : x^2 - 2 * x + 4 > 0 := by
          nlinarith [sq_nonneg (x - 1)]
        nlinarith
    · -- Case where 8 * x + 1 = 0
      have hx : x = -1 / 8 := by linarith
      left
      exact hx
  · -- Second direction: if x is a root (-1/8 or -2), then the polynomial is zero
    rintro (h | h)
    · -- Case where x = -1/8
      rw [h]
      norm_num
    · -- Case where x = -2
      rw [h]
      norm_num