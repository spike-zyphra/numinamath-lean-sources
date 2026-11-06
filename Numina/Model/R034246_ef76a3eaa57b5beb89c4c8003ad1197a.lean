import Mathlib

theorem algebra_204499 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h : y = x + 27) (h' : 900 / y = 600 / x) :
    x = 54 := by
  have h1 : y > 0 := by assumption
  have h2 : 900 * x = 600 * y := by
    field_simp [show y ≠ 0 by linarith, show x ≠ 0 by linarith] at h'
    linarith
  have h4 : 3 * x = 2 * y := by
    linarith
  rw [show y = x + 27 by linarith [h]] at h4
  linarith