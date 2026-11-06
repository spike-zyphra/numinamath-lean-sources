import Mathlib

theorem algebra_6794 {x : ℝ} (hx : x^2 - 6 * x + 1 = 0) (hx1 : x ≠ 0) :
    x^4 + 1 / x^4 = 1154 := by
  have h1 : x^2 = 6 * x - 1 := by linarith
  have eq1 : x ≠ 0 := hx1
  have h2 : x / x = 1 := by
    field_simp [eq1]
  have h3 : x + 1 / x = 6 := by
    have hx2 : x ≠ 0 := hx1
    field_simp [hx2] at *
    nlinarith
  have h4 : x^2 + 1 / x^2 = 34 := by
    have hx2 : x ≠ 0 := hx1
    field_simp [hx2] at *
    nlinarith [h3]
  have h5 : x^4 + 1 / x^4 = 1154 := by
    have hx2 : x ≠ 0 := hx1
    field_simp [hx2] at *
    nlinarith [h4]
  exact h5