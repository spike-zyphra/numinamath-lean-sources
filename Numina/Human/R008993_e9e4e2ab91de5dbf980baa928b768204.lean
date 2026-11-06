import Mathlib

/-There are four positive integers that are divisors of each number in the list $$36, 72, -12, 114, 96.$$Find the sum of these four positive integers.-/
theorem algebra_16763 : Nat.divisors 36 ∩ Nat.divisors 72 ∩ Nat.divisors (Int.natAbs (-12)) ∩
Nat.divisors 114 ∩ Nat.divisors 96 = {1,2,3,6} ∧ 1 + 2 + 3 + 6 = 12 := by
-- This is done be explicitly write out every set of divisors and find their intersection
  have d36 : Nat.divisors 36 = {1,2,3,4,6,9,12,18,36} := by decide
  have d72 : Nat.divisors 72 = {1,2,3,4,6,8,9,12,18,24,36,72} := by decide
  have dneg12 : Nat.divisors (Int.natAbs (-12)) = {1,2,3,4,6,12} := by decide
  have d114 : Nat.divisors 114 = {1,2,3,6,19,38,57,114} := by decide
  have d96 : Nat.divisors 96 = {1,2,3,4,6,8,12,16,24,32,48,96} := by decide
  rw [d36, d72, dneg12, d114, d96]; simp