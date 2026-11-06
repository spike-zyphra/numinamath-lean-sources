import Mathlib

theorem algebra_13600 {x : ℝ} (hx : x ≠ 0) (h : x^3 + 1/x^3 = 322) : x + 1/x = 7 := by
  have h1 : (x + 1/x)^3 = x^3 + 1/x^3 + 3*(x + 1/x) := by
    field_simp [hx]
    ring
  rw [h] at h1
  have h2 : (x + 1/x)^3 - 3*(x + 1/x) - 322 = 0 := by linarith
  have h3 : (x + 1/x - 7) * ((x + 1/x)^2 + 7*(x + 1/x) + 46) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case where $x + 1/x - 7 = 0$
    linarith
  · -- Case where $(x + 1/x)^2 + 7*(x + 1/x) + 46 = 0$
    nlinarith [sq_nonneg ((x + 1/x) + 7/2)]