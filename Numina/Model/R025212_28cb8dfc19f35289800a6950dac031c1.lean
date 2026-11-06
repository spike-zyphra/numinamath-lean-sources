import Mathlib

theorem number_theory_196991 (p : ℕ) (hp : p.Prime) :
    p % 30 = 1 ∨ (p % 30).Prime := by 
  by_cases h : p ≤ 30
  · -- p ≤ 30
    interval_cases p <;> norm_num at hp ⊢ <;> tauto
  · -- p > 30
    have h1 : p > 30 := by 
      linarith
    have h2 : p % 2 = 1 := by
      by_contra h
      push_neg at h
      have h3 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
        all_goals linarith
      contradiction
    -- p not divisible by 3
    have h3 : p % 3 = 1 ∨ p % 3 = 2 := by
      by_contra h
      push_neg at h
      have h4 : p % 3 = 0 := by omega
      have h6 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals linarith
      contradiction
    -- p not divisible by 5
    have h4 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by 
      by_contra h
      push_neg at h
      have h5 : p % 5 = 0 := by omega
      have h8 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega)
        all_goals linarith
      contradiction
    have : p % 30 = 1 ∨ p % 30 = 7 ∨ p % 30 = 11 ∨ p % 30 = 13 ∨ p % 30 = 17 ∨ p % 30 = 19 ∨ p % 30 = 23 ∨ p % 30 = 29 := by 
      omega
    rcases this with (h | h | h | h | h | h | h | h)
    · -- case p % 30 = 1
      left
      omega
    · -- case p % 30 = 7
      right
      rw [h]
      norm_num
    · -- case p % 30 = 11
      right
      rw [h]
      norm_num
    · -- case p % 30 = 13
      right
      rw [h]
      norm_num
    · -- case p % 30 = 17
      right
      rw [h]
      norm_num
    · -- case p % 30 = 19
      right
      rw [h]
      norm_num
    · -- case p % 30 = 23
      right
      rw [h]
      norm_num
    · -- case p % 30 = 29
      right
      rw [h]
      norm_num