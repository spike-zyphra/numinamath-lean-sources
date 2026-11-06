import Mathlib

theorem number_theory_239893 {n : ℕ} (hn : n ≠ 0) :
    (Nat.Prime (10 * n)) ∧ (Nat.Prime (15 * n)) ↔ False := by
  constructor
  · -- Assume both 10 * n and 15 * n are prime, prove False
    intro h
    rcases h with ⟨h1, h2⟩
    have h8 : n > 0 := by
      by_contra h'
      push_neg at h'
      have h9 : n = 0 := by omega
      contradiction
    have h4 : 10 * n ≥ 10 := by
      omega
    have h6 : ¬ Nat.Prime (10 * n) := by
      have h7 : 10 * n = 2 * (5 * n) := by ring
      rw [h7]
      have h8 : 2 > 1 := by norm_num
      have h9 : 5 * n > 1 := by
        nlinarith
      apply Nat.not_prime_mul (by omega) (by omega)
    contradiction
  · -- Assume False, prove both 10 * n and 15 * n are prime
    intro h
    exfalso
    exact h