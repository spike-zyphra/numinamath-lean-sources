import Mathlib

theorem number_theory_2066 (m n : ℕ) (h : Nat.Coprime m n) :
    Nat.totient (m * n) = Nat.totient m * Nat.totient n := by 
  rw [Nat.totient_mul]
  exact h