import Mathlib

theorem algebra_20013 {p q : ℕ} (hpq : p.Prime ∧ q.Prime) (hdiff : |(p : ℤ) - q| = 17) :
    p + q = 21 := by 
  have h1 : (p : ℤ) - q = 17 ∨ (p : ℤ) - q = -17 := by 
    cases' eq_or_eq_neg_of_abs_eq hdiff with h h
    · left
      linarith
    · right
      linarith
  rcases h1 with (h1 | h1)
  · -- p - q = 17
    have h2 : (p : ℤ) = q + 17 := by linarith 
    have hp1 : p = q + 17 := by
      norm_cast at h2 ⊢ 
    have hq : q = 2 := by 
      by_cases h : q % 2 = 1 
      · -- q is odd
        have h3 : p % 2 = 0 := by
          omega
        have hp3 : p.Prime := hpq.1 
        have hp : p > 2 := by 
          omega 
        have hp2 : ¬p.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
          all_goals 
            omega 
        have hp4 : p.Prime := hpq.1 
        exfalso 
        tauto 
      · -- q is even 
        have h7 : q = 2 := by 
          by_cases h8 : q > 2 
          · -- q > 2 even, contradicts prime 
            exfalso 
            have h9 : ¬q.Prime := by 
              apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
              all_goals
                omega 
            have h6 : q.Prime := hpq.2 
            tauto 
          · -- q <= 2. prime number <= 2 is 2 
            interval_cases q <;> norm_num at hpq ⊢ <;> tauto 
        assumption 
    have hp4 : p = 19 := by 
      omega 
    omega 
  · -- p - q = -17
    have h2 : (q : ℤ) = p + 17 := by 
      linarith 
    have hq2 : q = p + 17 := by 
      norm_cast at h2 ⊢ 
    by_cases h : p % 2 = 1 
    · -- p is odd
      have h9 : q % 2 = 0 := by 
        omega 
      have h10 : q > 2 := by 
        omega 
      have h6 : ¬q.Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
        all_goals 
          omega 
      have h4 : q.Prime := hpq.2 
      exfalso 
      tauto 
    · -- p is even
      have h4 : p = 2 := by 
        by_cases h5 : p > 2 
        · -- p > 2 even, contradicts prime 
          exfalso 
          have h9 : ¬p.Prime := by 
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
            all_goals 
              omega 
          have hp2 : p.Prime := hpq.1 
          tauto 
        · -- p <= 2. prime number <= 2 is 2
          interval_cases p <;> norm_num at hpq ⊢ <;> tauto 
      have h8 : q = 19 := by 
        omega 
      omega