import Mathlib

theorem algebra_612687 {a b : ℝ} (h : a^2 - 11*a*b - 60 = 0) (ha : a ≠ 0) :
    b = (a^2 - 60)/(11*a) := by
  have h1 : 11 * a * b = a^2 - 60 := by linarith
  have h2 : b = (a^2 - 60) / (11 * a) := by
    field_simp [ha]
    linarith
  exact h2