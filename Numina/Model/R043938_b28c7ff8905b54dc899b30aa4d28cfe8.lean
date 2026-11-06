import Mathlib

theorem number_theory_323691
    (p q : ℕ)
    (hp : p.Prime)
    (hq : q.Prime)
    (h1 : (7 * p + q).Prime)
    (h2 : (p * q + 11).Prime) :
    (p ^ 2 + q ^ p) * (q ^ 2 + p ^ q) = 221 := by
  by_cases h3 : p % 2 = 1
  · -- Assume p is odd
    by_cases h4 : q % 2 = 1
    · -- Assume both p and q are odd
      have h4' : (7 * p + q) % 2 = 0 := by
        omega
      have h5 : ¬(7 * p + q).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (7 * p + q) by omega)
        all_goals
        have : 7 * p + q > 2 := by
          have hp3 : p ≥ 3 := by
            by_contra h
            push_neg at h
            interval_cases p <;> norm_num at hp h3 ⊢ <;> try { contradiction } <;> norm_num at h3 h4 hp h1 h2 h4' ⊢
            <;> try { contradiction }
          have hq3 : q ≥ 3 := by
            by_contra h
            push_neg at h
            interval_cases q <;> norm_num at hq h4 ⊢ <;> try { contradiction } <;> norm_num at hq h4 h3 hp h1 h2 h4' ⊢
            <;> try { contradiction }
          omega
        all_goals linarith
      contradiction
    · -- Assume q is even
      have h4' : q = 2 := by
        by_cases h4' : q > 2
        · -- Assume q > 2, then q must be odd, contradiction
          have h41 : q % 2 = 1 := by
            by_contra h
            push_neg at h
            have h4' : ¬q.Prime := by
              apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
              all_goals omega
            contradiction
          omega
        · -- q ≤ 2, then q = 2
          interval_cases q <;> norm_num at hq h4 ⊢ <;> try { contradiction }
          <;> try { contradiction }
          <;> norm_num
      subst q
      by_cases hp2 : p ≤ 13
      · -- p ≤ 13, try all odd primes up to 13
        interval_cases p <;> norm_num at hp h1 h2 ⊢ <;> try { contradiction } <;> norm_num
      · -- Assume p > 13
        have h14 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
          omega
        rcases h14 with (h | h | h)
        · -- Assume p ≡ 0 (mod 3)
          -- If p ≡ 0 (mod 3) and p is prime, then p = 3
          have : p = 3 := by
            by_cases h15 : p ≤ 3
            · -- p ≤ 3, then p = 3
              interval_cases p <;> norm_num at hp h1 h2 h ⊢ <;> try { contradiction }
              <;> norm_num at hp h1 h2 h ⊢
            · -- p > 3, then p is divisible by 3 and not prime
              have hp3ne : p > 3 := by
                omega
              exfalso
              have hp3 : ¬p.Prime := by
                apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
                all_goals omega
              contradiction
          subst p
          norm_num at hp h1 h2 ⊢
          all_goals try { contradiction }
          all_goals norm_num
        · -- Assume p ≡ 1 (mod 3)
          have hp3ne : 7 * p + 2 > 2 := by
            have : p ≥ 4 := by
              by_contra h
              push_neg at h
              interval_cases p <;> norm_num at hp h1 h2 h ⊢ <;> try { contradiction }
              <;> try { contradiction }
            omega
          have : (7 * p + 2) % 3 = 0 := by
            omega
          have h5 : ¬(7 * p + 2).Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (7 * p + 2) by omega)
            all_goals omega
            all_goals linarith
          contradiction
        · -- Assume p ≡ 2 (mod 3)
          have hp3ne : p * 2 + 11 > 2 := by
            have : p ≥ 4 := by
              by_contra h
              push_neg at h
              interval_cases p <;> norm_num at hp h1 h2 h ⊢ <;> try { contradiction }
              <;> try { contradiction }
            omega
          have : (p * 2 + 11) % 3 = 0 := by
            omega
          have h5 : ¬(p * 2 + 11).Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p * 2 + 11) by omega)
            all_goals omega
            all_goals linarith
          contradiction
  · -- Assume p is even, so p = 2
    have p2 : p = 2 := by
      by_cases hp2 : p > 2
      · -- Assume p > 2
        have : p % 2 = 0 := by
          omega
        have hp3ne : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
          all_goals omega
        contradiction
      · -- p ≤ 2
        interval_cases p <;> norm_num at hp h3 ⊢ <;> try { contradiction }
    subst p
    by_cases hq2 : q ≤ 5
    · -- Assume q ≤ 5
      interval_cases q <;> norm_num at hq h1 h2 ⊢ <;> try { contradiction }
      <;> norm_num
    · -- Assume q > 5
      have h14 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by
        omega
      rcases h14 with (h | h | h)
      · -- Assume q ≡ 0 (mod 3)
        -- If q ≡ 0 (mod 3) and q is prime, then q = 3
        have : q = 3 := by
          by_cases h15 : q ≤ 3
          · -- q ≤ 3, then q = 3
            interval_cases q <;> norm_num at hq h1 h2 h ⊢ <;> try { contradiction }
            <;> norm_num at hq h1 h2 h ⊢
          · -- q > 3, then q is divisible by 3 and not prime
            have hq3ne : q > 3 := by
              omega
            exfalso
            have hq3 : ¬q.Prime := by
              apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ q by omega)
              all_goals omega
            contradiction
        subst q
        norm_num at hp h1 h2 hq ⊢
        all_goals try { contradiction }
        all_goals norm_num
      · -- Assume q ≡ 1 (mod 3)
        have hq3ne : 14 + q > 2 := by
          have : q ≥ 4 := by
            by_contra h
            push_neg at h
            interval_cases q <;> norm_num at hq h1 h2 h ⊢ <;> try { contradiction }
            <;> try { contradiction }
          omega
        have : (14 + q) % 3 = 0 := by
          omega
        have h5 : ¬(14 + q).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (14 + q) by omega)
          all_goals omega
          all_goals linarith
        contradiction
      · -- Assume q ≡ 2 (mod 3)
        have hq3ne : 2 * q + 11 > 2 := by
          have : q ≥ 4 := by
            by_contra h
            push_neg at h
            interval_cases q <;> norm_num at hq h1 h2 h ⊢ <;> try { contradiction }
            <;> try { contradiction }
          omega
        have : (2 * q + 11) % 3 = 0 := by
          omega
        have h5 : ¬(2 * q + 11).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (2 * q + 11) by omega)
          all_goals omega
          all_goals linarith
        contradiction