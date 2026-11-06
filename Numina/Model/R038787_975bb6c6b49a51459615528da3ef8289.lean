import Mathlib

theorem number_theory_14768 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h : 11 * p + 1 = q) : q = 23 := by
  by_cases h1 : p ≤ 3
  · -- Case p ≤ 3
    have hp2 : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by 
      interval_cases p <;> omega
    rcases hp2 with (r | r | r | r)
    · -- p = 0
      rw [r] at hp
      norm_num at hp 
    · -- p = 1
      rw [r] at hp 
      norm_num at hp 
    · -- p = 2
      rw [r] at h 
      have hq23 : q = 23 := by
        omega 
      exact_mod_cast hq23 
    · -- p = 3 
      rw [r] at h 
      have hq34 : q = 34 := by
        omega 
      rw [hq34] at hq 
      norm_num at hq 
  · -- Case p > 3 
    have h1 : p > 3 := by
      by_contra h2
      push_neg at h2
      have : p ≤ 3 := by linarith
      linarith
    have h2 : p % 2 = 1 := by
      by_contra h3
      push_neg at h3
      have h4 : p % 2 = 0 := by omega
      have h5 : p > 2 := by
        omega
      have h6 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
        all_goals linarith
      contradiction
    have h3 : q % 2 = 0 := by
      omega
    by_cases h4 : q > 2
    · -- When q > 2.
      have h5 : ¬q.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
        all_goals omega
      contradiction
    · -- When q ≤ 2. Then q = 0, 1, or 2.
      have h6 : q ≤ 2 := by omega
      have h7 : q = 0 ∨ q = 1 ∨ q = 2 := by 
        omega
      rcases h7 with (h8 | h8 | h8)
      · -- q = 0
        rw [h8] at h 
        have h8 : p = 0 := by
          omega 
        rw [h8] at hp 
        norm_num at hp 
      · -- q = 1 
        rw [h8] at h 
        have h8 : p = 0 := by
          omega 
        rw [h8] at hp 
        norm_num at hp 
      · -- q = 2 
        rw [h8] at h 
        omega