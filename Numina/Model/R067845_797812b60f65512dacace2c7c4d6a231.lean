import Mathlib

theorem algebra_293734 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h : (x + y) / x = 2 * (x - y) / x) : x / y = 3 := by
-- Assume x > 0 and y > 0, so denominators are well-defined
  have h1 : x ≠ 0 := by linarith
  have eq1 : x + y = 2 * (x - y) := by
    have h2 : x ≠ 0 := by linarith
    field_simp [h2] at h ⊢
    linarith
  -- Simplify equation
  have eq2 : x = 3 * y := by
    linarith [eq1]
  -- Convert to fraction
  have eq3 : y ≠ 0 := by linarith
  field_simp [eq3]
  <;> nlinarith [eq2, hy]