import Mathlib

theorem number_theory_248496 : IsGreatest {n : ℕ | ∀ p, p.Prime → Odd p → p < n → (n - p).Prime} 10 := by

  constructor
  · -- Show 10 is in the set.
    show ∀ p, p.Prime → Odd p → p < 10 → (10 - p).Prime
    intro p hp h_odd hp_lt
    have h1 : p ≤ 9 := by linarith
    interval_cases p <;> norm_num at hp h_odd hp_lt ⊢ <;> tauto

  · -- Show 10 is greatest.
    intro n hn
    have h10 : ∀ p, p.Prime → Odd p → p < n → (n - p).Prime := hn

    by_contra h
    push_neg at h

    have h11 : n > 10 := h

    by_cases h14 : n ≤ 20
    · -- 11 ≤ n ≤ 20
      interval_cases n <;> try { 
        norm_num at h11 ⊢ 
        all_goals
        try { 
          have h3' := h10 3 (by norm_num) (by decide) (by norm_num)
          norm_num at h3'
        }
        all_goals
        try { 
          have h5' := h10 5 (by norm_num) (by decide) (by norm_num)
          norm_num at h5'
        }
        all_goals
        try { 
          have h7' := h10 7 (by norm_num) (by decide) (by norm_num)
          norm_num at h7'
        }
        all_goals
        try { 
          tauto
        }
      }
    · -- n > 20
      have h3' := h10 3 (by norm_num) (by decide) (by
        omega
      )
      by_cases h17 : n % 3 = 0
      · -- n ≡ 0 [3]
        have h4 : (n - 3) % 3 = 0 := by
          omega
        have h5 : ¬ (n - 3).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (n - 3) by omega)
          all_goals
          omega
        have h5' : (n - 3).Prime := h3'
        contradiction
      · -- n % 3 = 1 or 2
        have h18 : n % 3 = 1 ∨ n % 3 = 2 := by
          omega
        rcases h18 with (h18 | h18)
        · -- n % 3 = 1
          have h3' := h10 7 (by norm_num) (by decide) (by
            omega
          )
          by_cases h25 : n ≤ 22
          · -- 11 < n ≤ 22
            interval_cases n <;> norm_num at h3' h11 h18
          · -- n > 22
            have h4 : (n - 7) % 3 = 0 := by
              omega
            have h5 : ¬ (n - 7).Prime := by
              apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (n - 7) by omega)
              all_goals
              omega
            have h5' : (n - 7).Prime := h3'
            contradiction
        · -- n % 3 = 2
          have h3' := h10 5 (by norm_num) (by decide) (by
            omega
          )
          by_cases h25 : n ≤ 26
          · -- 11 < n ≤ 26
            interval_cases n <;> norm_num at h3' h11 h18
          · -- n > 26
            have h4 : (n - 5) % 3 = 0 := by
              omega
            have h5 : ¬ (n - 5).Prime := by
              apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (n - 5) by omega)
              all_goals
              omega
            have h5' : (n - 5).Prime := h3'
            contradiction