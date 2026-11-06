import Mathlib

theorem algebra_4814 {x : ℚ} (hx : x > 0) (hx1 : x = 6 / (5 + x)) : x = 1 := by
  have h1 : x * (5 + x) = 6 := by
    have h2 : 5 + x ≠ 0 := by
      linarith
    field_simp [h2] at hx1
    nlinarith
  have h2 : x ^ 2 + 5 * x - 6 = 0 := by
    nlinarith [h1]
  have h3 : (x - 1) * (x + 6) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h3) with h4 h5
  · 
    linarith
  · 
    linarith