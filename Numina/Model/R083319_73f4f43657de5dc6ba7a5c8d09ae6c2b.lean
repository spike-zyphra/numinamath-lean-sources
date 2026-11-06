import Mathlib

theorem algebra_186655 (x : ℝ) (hx : x ≠ 0) (h : 4 / (x ^ 2 + 4) + 5 / (x ^ 2 + 5) = 2) :
    x = 0 := by
  have h1 : x^2 + 4 > 0 := by
    nlinarith [sq_nonneg x]
  have h2 : x^2 + 5 > 0 := by
    nlinarith [sq_nonneg x]
  have h3 : 4 * (x^2 + 5) + 5 * (x^2 + 4) = 2 * (x^2 + 4) * (x^2 + 5) := by
    have eq1 : (x^2 + 4) * (x^2 + 5) ≠ 0 := by
      positivity
    field_simp [(show x^2 + 4 ≠ 0 by linarith [h1]), (show x^2 + 5 ≠ 0 by linarith [h2])] at h ⊢
    nlinarith
  have h4 : 2 * x^4 + 9 * x^2 = 0 := by
    nlinarith [sq_nonneg (x^2)]
  have h5 : x^2 * (2 * x^2 + 9) = 0 := by
    nlinarith [sq_nonneg (x^2)]
  cases' (mul_eq_zero.mp h5) with h51 h52
  · -- h51 : x^2 = 0
    have h6 : x = 0 := by
      nlinarith
    contradiction
  · -- h52 : 2 * x^2 + 9 = 0
    nlinarith [sq_nonneg x, sq_nonneg (x^2)]