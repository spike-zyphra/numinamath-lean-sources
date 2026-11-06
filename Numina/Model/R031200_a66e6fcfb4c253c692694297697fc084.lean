import Mathlib

theorem number_theory_242063 : ∀ n, ∃ p > n, p.Prime ∧ p ∈ {x | ∃ k, x = 8 * k + 1} := by
  intro n
  have h : ∃ p, p ≥ n + 1 ∧ p.Prime ∧ (p % 8 = 1) := by
    have h_infinite : (setOf (fun p : ℕ => p.Prime ∧ p % 8 = 1)).Infinite := by
      apply Nat.infinite_setOf_prime_modEq_one
      all_goals norm_num
    obtain ⟨p, hp, hp_gt⟩ := h_infinite.exists_gt (n)
    have hp_prime: p.Prime := hp.1
    have hp_mod : p % 8 = 1 := hp.2
    have hp_ge : p > n := by 
      linarith
    have hp_ge2 : p ≥ n + 1 := by 
      omega
    exact ⟨p, hp_ge2, hp_prime, hp_mod⟩
  rcases h with ⟨p, hp_ge, hp_prime, hp_mod⟩
  use p
  constructor
  · linarith
  constructor
  · exact hp_prime
  · refine ⟨(p - 1) / 8, by omega⟩