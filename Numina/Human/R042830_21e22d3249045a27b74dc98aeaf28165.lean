import Mathlib

theorem algebra_5642
    (a b : ℕ) :
    a * b = b * a := by
  rw [Nat.mul_comm]