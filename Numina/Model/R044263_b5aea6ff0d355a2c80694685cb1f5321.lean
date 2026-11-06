import Mathlib

theorem number_theory_197070 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hsum : p + q = 105) :
    p * q = 206 := by
  have h1 : p ≤ 105 := by
    omega
  have h2 : q ≤ 105 := by
    omega
  by_cases h4 : p > 2
  · -- Assume p > 2, then p must be odd, which forces q = 2
    have h5 : q = 2 := by
      have h5 : p % 2 = 1 := by
        by_contra h
        push_neg at h
        have h6 : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
          all_goals
          omega
        contradiction
      have h5 : q % 2 = 0 := by
        omega
      by_cases h6 : q > 2
      · -- Assume q > 2, then not prime
        have h7 : ¬q.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
          all_goals
          omega
        contradiction
      · -- q ≤ 2.
        interval_cases q <;> norm_num at hq hsum ⊢ <;> omega
    have h6 : p = 103 := by
      omega
    norm_num [h6, h5] at *
  · -- p ≤ 2.
    have h4 : p = 0 ∨ p = 1 ∨ p = 2 := by 
      interval_cases p <;> omega
    rcases h4 with (h4 | h4 | h4)
    · -- p = 0
      rw [h4] at hp 
      norm_num at hp
    · -- p = 1
      rw [h4] at hp 
      norm_num at hp
    · -- p = 2
      have h8 : q = 103 := by 
        omega
      norm_num [h4, h8] at *