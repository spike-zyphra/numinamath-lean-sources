import Mathlib

theorem number_theory_97352 : ¬∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 10001 := by
  rintro ⟨p, q, hp, hq, hsum⟩
  have h3 : p = 2 ∨ q = 2 := by
    by_cases h4 : p % 2 = 0
    · -- Assume p % 2 = 0
      have h5 : p = 2 := by
        by_cases h6 : p > 2
        · -- Assume p > 2
          have h7 : ¬p.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
            all_goals omega
          contradiction
        · -- Assume p ≤ 2
          interval_cases p <;> norm_num at hp <;> tauto
      left
      exact h5
    · -- Assume p % 2 ≠ 0, then q % 2 = 0
      have h8 : q % 2 = 0 := by
        omega
      have h9 : q = 2 := by
        by_cases h10 : q > 2
        · -- Assume q > 2
          have h11 : ¬q.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
            all_goals omega
          contradiction
        · -- Assume q ≤ 2
          interval_cases q <;> norm_num at hq <;> tauto
      right
      exact h9
  rcases h3 with (h | h)
  · -- Assume p = 2
    have hp2 : p = 2 := h
    have hq2 : q = 9999 := by
      omega
    rw [hq2] at hq
    norm_num at hq
  · -- Assume q = 2
    have hq2 : q = 2 := h
    have hp2 : p = 9999 := by
      omega
    rw [hp2] at hp
    norm_num at hp