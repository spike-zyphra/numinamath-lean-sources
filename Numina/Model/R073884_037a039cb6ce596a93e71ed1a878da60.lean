import Mathlib

theorem algebra_302588 {a b c : ℤ} (ha : a ≠ 0) (h1 : a * 1^2 + b * 1 + c = 0)
    (h2 : Even (a * (-1)^2 + b * (-1) + c)) :
    ∃ x1 x2 : ℤ, x1^2 - (a + b + c) * x1 + b * a + b * c = 0 ∧
    x2^2 - (a + b + c) * x2 + b * a + b * c = 0 := by
  have h3 : a + b + c = 0 := by linarith
  have h4 : b * a + b * c = -b^2 := by
    have eq1 : a + c = -b := by linarith [h3]
    calc
      b * a + b * c = b * (a + c) := by ring
      _ = b * (-b) := by rw [eq1]
      _ = -b^2 := by ring
  use b, -b 
  constructor 
  · -- Show that b is a root.
    have eq1 : b ^ 2 - (a + b + c) * b + b * a + b * c = 0 := by
      rw [show a + b + c = 0 by linarith [h3]]
      nlinarith [show b * a + b * c = -b^2 by linarith [h4], sq_nonneg b]
    exact eq1 
  · -- Show that -b is a root.
    have eq1 : (-b) ^ 2 - (a + b + c) * (-b) + b * a + b * c = 0 := by
      rw [show a + b + c = 0 by linarith [h3]]
      nlinarith [show b * a + b * c = -b^2 by linarith [h4], sq_nonneg b]
    exact eq1