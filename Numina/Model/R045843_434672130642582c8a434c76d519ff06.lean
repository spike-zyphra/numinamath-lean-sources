import Mathlib

theorem number_theory_233542 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hsum : p + q > 10) (hodd : Odd (p + q)) :
    (p + q) % 10 = 1 ∨ (p + q) % 10 = 3 ∨ (p + q) % 10 = 5 ∨ (p + q) % 10 = 9 := by
  have h1 : p % 2 = 0 ∨ q % 2 = 0 := by 
    by_contra h 
    push_neg at h 
    have h2 : p % 2 = 1 := by 
      omega 
    have h3 : q % 2 = 1 := by 
      omega 
    have : (p + q) % 2 = 0 := by 
      omega 
    have h4 : ¬Odd (p + q) := by 
      simp [Nat.odd_iff] at *
      all_goals omega 
    tauto 

  have h2 : p = 2 ∨ q = 2 := by 
    by_cases hp2 : p % 2 = 0 
    · -- p is even, and prime, so p = 2 
      have hp2_eq : p = 2 := by 
        by_cases hp1 : p > 2 
        · -- p > 2 and even, so not prime 
          have h6 : ¬p.Prime := by 
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) 
            all_goals omega 
          contradiction 
        · -- p ≤ 2, prime and even -> p = 2 
          interval_cases p <;> trivial 
      left 
      tauto 
    · -- not hp2, so q % 2 = 0 
      have hq2_eq : q = 2 := by 
        by_cases hq1 : q > 2 
        · -- q > 2 and even, so not prime 
          have h6 : ¬q.Prime := by 
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega) 
            all_goals omega 
          contradiction 
        · -- q ≤ 2, prime and even -> q = 2 
          interval_cases q <;> trivial 
      right 
      tauto 

  cases h2 with 
  | inl hp2_eq => 
    subst p 
    by_cases hq1 : q ≤ 10 
    · -- contradiction 
      interval_cases q <;> norm_num at hq hp hsum hodd <;> tauto 
    · -- q > 10 
      have hq1 : q % 10 = 1 ∨ q % 10 = 3 ∨ q % 10 = 7 ∨ q % 10 = 9 := by 
        by_cases h1 : q % 2 = 0 
        · -- contradiction, q even, prime implies q = 2, which is invalid here 
          have h6 : ¬q.Prime := by 
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega) 
            all_goals omega 
          contradiction 
        · -- q not even 
          by_cases h1 : q % 5 = 0 
          · -- contradiction, divisible by 5 
            have h6 : ¬q.Prime := by 
              apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ q by omega) 
              all_goals omega 
            contradiction 
          · -- q not divisible by 2 or 5 
            omega 
      omega 
  | inr hq2_eq => 
    subst q 
    by_cases hp1 : p ≤ 10 
    · -- contradiction 
      interval_cases p <;> norm_num at hq hp hsum hodd <;> tauto 
    · -- p > 10 
      have hp1 : p % 10 = 1 ∨ p % 10 = 3 ∨ p % 10 = 7 ∨ p % 10 = 9 := by 
        by_cases h1 : p % 2 = 0 
        · -- contradiction, p even, prime implies p = 2, which is invalid here 
          have h6 : ¬p.Prime := by 
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) 
            all_goals omega 
          contradiction 
        · -- p not even 
          by_cases h1 : p % 5 = 0 
          · -- contradiction, divisible by 5 
            have h6 : ¬p.Prime := by 
              apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega) 
              all_goals omega 
            contradiction 
          · -- p not divisible by 2 or 5 
            omega 
      omega