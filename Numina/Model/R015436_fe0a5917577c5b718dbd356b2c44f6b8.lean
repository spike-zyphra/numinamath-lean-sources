import Mathlib

theorem algebra_13407 {x : ℚ} (hx : x > 0) (h : x = 5 + 6 / (5 + 6 / (5 + 6 / x))) : x = 6 := by
  have hx1 : x ≠ 0 := by linarith
  field_simp [hx1] at h
  have h1 : (31 * x ^ 2 - 155 * x - 186) = 0 := by
    nlinarith
  have h2 : (x - 6) * (x + 1) = 0 := by
    nlinarith [h1]
  cases' (mul_eq_zero.1 h2) with h3 h4
  · -- x - 6 = 0 ⊢ x = 6
    linarith
  · -- x + 1 = 0 ⊢ x = -1
    have hx2 : x = -1 := by linarith
    linarith