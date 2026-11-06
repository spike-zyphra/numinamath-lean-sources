import Mathlib

theorem algebra_14247 (x : ℕ) (hx : x = 10  ^ 100 * 6 / 7): (Nat.digits 10 (x)).length = 100 ∧ (Nat.digits 10 (x))[0]! = 1 := by
  rw [hx]
  constructor
  · -- Show that the length of digits is 100
    native_decide
  · -- Show that the last digit is 1
    native_decide