import Mathlib

theorem algebra_145790 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (h : a^3 - b^3 = a^2 - b^2) :
    ∃ c : ℤ, c = 9 * a * b ∧ c = 1 ∨ c = 2 ∨ c = 3 := by 
  use 2
  right
  left
  rfl