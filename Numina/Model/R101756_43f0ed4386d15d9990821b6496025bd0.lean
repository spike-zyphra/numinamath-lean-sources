import Mathlib

theorem algebra_301421 {a b c : ℤ} (ha : a ≠ 0) (h1 : a * 1^2 + b * 1 + c = 0)
    (h2 : Even (a * (-1)^2 + b * (-1) + c)) :
    ∃ x1 x2 : ℤ, x1^2 - (a + b + c) * x1 + b * a + b * c = 0 ∧
    x2^2 - (a + b + c) * x2 + b * a + b * c = 0 := by 
  have h3 : c = -a - b := by
    linarith
  use b, -b
  constructor
  · -- Let's check b
    rw [h3]
    ring
  · -- Let's check -b
    rw [h3]
    ring