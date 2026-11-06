import Mathlib

theorem algebra_16763 : Nat.divisors 36 ∩ Nat.divisors 72 ∩ Nat.divisors (Int.natAbs (-12)) ∩
Nat.divisors 114 ∩ Nat.divisors 96 = {1,2,3,6} ∧ 1 + 2 + 3 + 6 = 12 := by
  constructor
  · -- This will be solved by computational methods
    native_decide
  · -- Trivial arithmetic
    norm_num