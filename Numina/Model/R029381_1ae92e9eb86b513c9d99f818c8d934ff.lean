import Mathlib

theorem number_theory_86147 :
    ∃ n, IsSquare n ∧ (Nat.digits 10 n).sum = 2011 := by
  use (10 ^ 223 - 3) ^ 2
  constructor
  · -- Show that n is a perfect square
    native_decide
  · -- Show that the sum of digits is 2011
    native_decide