import Mathlib


theorem algebra_91813 {x y : ℝ} (h : x^3 + x^2 * y + x * y^2 + y^3 = 8 * (x^2 + x * y + y^2 + 1)) :
    (x = 8 ∧ y = -2) ∨ (x = -2 ∧ y = 8) ∨
    ∃ a b, x = a + b * Real.sqrt 15 ∧ y = a - b * Real.sqrt 15 := by

  right
  right
  use (x + y) / 2, (x - y) / (2 * Real.sqrt 15)
  constructor
  · -- Show x = a + b * Real.sqrt 15
    field_simp [Real.sqrt_ne_zero']
    <;> nlinarith
  · -- Show y = a - b * Real.sqrt 15
    field_simp [Real.sqrt_ne_zero']
    <;> nlinarith