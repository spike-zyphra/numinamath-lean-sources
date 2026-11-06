import Mathlib

theorem number_theory_4884_1 (p t : ℕ) [hp : Fact (Nat.Prime p)] (ht : 1 ≤ t) :
    (p ^ t).totient = p ^ t - p ^ (t - 1) := by
  --The problem is exactly the proposition Nat.totient_prime_pow in Mathlib.
  rw [Nat.totient_prime_pow, Nat.mul_sub_left_distrib]
  nth_rw 2 [← Nat.pow_one p]; rw [← Nat.pow_add, ← Nat.sub_add_comm]
  simp; exact ht; exact hp.1; linarith

theorem number_theory_4884_2 : ∀ {m n : ℕ}, Nat.Coprime m n →
    Nat.totient (m * n) = Nat.totient m * Nat.totient n := by
  intro m n h_coprime
  rw [Nat.totient_mul]
  exact h_coprime