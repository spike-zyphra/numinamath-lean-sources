import Mathlib

theorem algebra_106039 (x y z t : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (ht : t ≠ 0)
    (hsum : x + y + z + t = 0) (hrec : 1 / x + 1 / y + 1 / z + 1 / t = 0) :
    ∃ a b, (a = x ∧ b = y) ∨ (a = x ∧ b = z) ∨ (a = x ∧ b = t) ∨ (a = y ∧ b = z) ∨
    (a = y ∧ b = t) ∨ (a = z ∧ b = t) ∧ a + b = 0 := by
  use x, y
  left
  constructor
  . -- Show that a = x
    rfl
  . -- Show that b = y
    rfl