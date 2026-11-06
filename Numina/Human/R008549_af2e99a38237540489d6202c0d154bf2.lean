import Mathlib

theorem algebra_10306 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h₀ : b / a = 3) (h₁ : b = 12 - 5 * a) :
    a = 3 / 2 := by
  field_simp at *
  linarith