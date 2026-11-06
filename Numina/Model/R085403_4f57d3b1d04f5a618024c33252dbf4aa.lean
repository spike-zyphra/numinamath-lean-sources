import Mathlib

theorem number_theory_133229 : (Nat.digits 10 ((2^3 * 5^4 * 10^5) : ℕ)).length = 9 := by
  norm_num [Nat.digits, Nat.digitsAux]