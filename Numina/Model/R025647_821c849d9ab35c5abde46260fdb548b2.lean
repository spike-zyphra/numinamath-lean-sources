import Mathlib

theorem number_theory_106948 (p : ℕ) (hp : p.Prime) :
    ¬∃ n, n ≠ 0 ∧ n < 30 ∧ n > 1 ∧ ¬n.Prime ∧ p % 30 = n := by
  rintro ⟨n, hn1, hn2, hn3, hn4, h⟩
  have h1 : n < 30 := by linarith
  interval_cases n <;> norm_num at hn4 h ⊢ <;> try { 
    have h2 : p % 2 = 0 ∨ p % 3 = 0 ∨ p % 5 = 0 := by
      omega
    by_cases h8 : p > 5
    · -- Assume p > 5
      have hp2 : p % 2 = 1 := by
        by_contra h
        push_neg at h
        have h2 : p % 2 = 0 := by omega
        have h4 : ¬p.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
          all_goals omega
        tauto
      have hp3 : p % 3 = 1 ∨ p % 3 = 2 := by
        by_contra h
        push_neg at h
        have h2 : p % 3 = 0 := by omega
        have h4 : ¬p.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
          all_goals omega
        tauto
      have hp5 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
        by_contra h
        push_neg at h
        have h2 : p % 5 = 0 := by omega
        have h4 : ¬p.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega)
          all_goals omega
        tauto
      omega
    · -- Assume p ≤ 5
      interval_cases p <;> norm_num at hp h ⊢ <;> omega
  }