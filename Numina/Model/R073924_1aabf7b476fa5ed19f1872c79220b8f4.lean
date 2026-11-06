import Mathlib

theorem number_theory_114411 (n : ℕ) (hn : 2 ≤ n) :
    ∃ a b, a + b = n ∧ Nat.Coprime a b := by 
  use 1, n - 1
  constructor
  · -- Show that 1 + (n - 1) = n
    omega
  · -- Show that gcd(1, n - 1) = 1
    simp