import Mathlib

theorem algebra_21125 : Nat.gcd (6^3 : ℕ) (3^6 : ℕ) = 27 := by
  norm_num [Nat.gcd]