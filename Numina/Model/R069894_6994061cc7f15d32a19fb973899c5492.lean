import Mathlib

theorem algebra_15265 (x : ℝ) (hx : x^4 - 2 * x^3 - x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 : (x - 1) * (x - 2) * (x^2 + x + 1) = 0 := by
    nlinarith [sq_nonneg (x^2), sq_nonneg (x - 1), sq_nonneg (x - 2)]
  cases' (mul_eq_zero.mp h1) with h2 h3
  · cases' (mul_eq_zero.mp h2) with h4 h5
    · left
      linarith
    · right
      linarith
  · -- Show that x^2 + x + 1 = 0 has no real solutions
    have h6 : x^2 + x + 1 > 0 := by 
      nlinarith [sq_nonneg (x + 0.5)]
    linarith