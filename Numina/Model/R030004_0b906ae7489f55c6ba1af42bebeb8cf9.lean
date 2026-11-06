import Mathlib

theorem number_theory_4860 : ∀ {m n : ℕ}, Nat.Coprime m n →
    Nat.totient (m * n) = Nat.totient m * Nat.totient n := by 
  intro m n h
  rw [Nat.totient_mul]
  exact h