import Mathlib

open scoped BigOperators

theorem algebra_5178 {x : ℚ} (hx1 : x > 0) (hx2:  x = 44 / (7 + x)) : x = 4 := by
  have h1 : x * (7 + x) = 44 := by
    have h1 : 7 + x ≠ 0 := by
      linarith [hx1]
    field_simp [h1] at hx2 ⊢
    linarith [hx2]
  have h2 : x^2 + 7 * x - 44 = 0 := by
    nlinarith [h1]
  have h3 : (x - 4) * (x + 11) = 0 := by
    nlinarith [h2]
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case where x - 4 = 0, so x = 4
    linarith
  · -- Case where x + 11 = 0, so x = -11, which contradicts x > 0
    linarith