import Mathlib

theorem number_theory_69848 (n : ℕ) :
    ∃ m, m % (2 ^ n) = 0 ∧ ∀ d ∈ Nat.digits 10 m, d ≠ 0 := by 
  use 0
  constructor
  · -- Show 0 % (2 ^ n) = 0
    simp
  · -- Show that all digits of 0 are non-zero (trivially true since 0 has no digits)
    intro d hd
    simpa using hd -- Nat.digits 10 0 = [] so this is contradiction