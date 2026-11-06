import Mathlib

/-Let K be the integer 2. Show that there exists a natural number
n such that the product of the base-10 digits of n is non-zero, the product of the base-10 digits of n+1 is non-zero,
and the product of the digits of n+1 is K times the product of the digits of n. For example,
n=1 is such a number.-/

theorem number_theory_636196 (K: ℕ) (h: K = 2):
  ∃ n : ℕ, (Nat.digits 10 n).prod ≠ 0 ∧ (Nat.digits 10 (n + 1)).prod ≠ 0 ∧
  (Nat.digits 10 (n + 1)).prod = K * (Nat.digits 10 n).prod := by

  use 11
  simp [h]