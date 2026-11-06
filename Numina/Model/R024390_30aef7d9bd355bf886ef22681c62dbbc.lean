import Mathlib

theorem number_theory_226433 (p : ℕ) (hp : Nat.Prime p) :
    Nat.Prime (p % 30) ∨ p % 30 = 1 := by
  by_cases h : p ≤ 30
  · -- p ≤ 30
    interval_cases p <;> norm_num at hp ⊢ <;> tauto
  · -- p > 30
    have h1 : p % 2 = 1 := by
      by_contra h2
      push_neg at h2
      have h2' : p % 2 = 0 := by omega 
      have h2'' : ¬Nat.Prime p := by 
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) 
        all_goals linarith 
      tauto
    by_cases h2 : p % 3 = 0 
    · -- p % 3 = 0 
      have h2'' : ¬Nat.Prime p := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) 
        all_goals linarith 
      tauto 
    by_cases h3 : p % 5 = 0 
    · -- p % 5 = 0 
      have h3'' : ¬Nat.Prime p := by 
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega) 
        all_goals linarith 
      tauto 
    -- Now p is not divisible by 2, 3, 5
    have h4 : p % 2 = 1 := h1 
    have h5 : p % 3 = 1 ∨ p % 3 = 2 := by 
      omega 
    have h6 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by 
      omega 
    -- Now we need to figure out all the residues
    -- The proof strategy is to now show all possible residues
    -- We need to show that the possible residues are 
    -- 1,7,11,13,17,19,23,29
    -- and then show they're either prime or 1
    have h7 : p % 30 = 1 ∨ p % 30 = 7 ∨ p % 30 = 11 ∨ p % 30 = 13 ∨ p % 30 = 17 ∨ p % 30 = 19 ∨ p % 30 = 23 ∨ p % 30 = 29 := by
      omega 
    rcases h7 with (h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7)
    · -- p % 30 = 1 
      tauto 
    · -- p % 30 = 7 
      rw [h7] 
      norm_num 
    · -- p % 30 = 11 
      rw [h7] 
      norm_num 
    · -- p % 30 = 13 
      rw [h7] 
      norm_num 
    · -- p % 30 = 17 
      rw [h7] 
      norm_num 
    · -- p % 30 = 19 
      rw [h7] 
      norm_num 
    · -- p % 30 = 23 
      rw [h7] 
      norm_num 
    · -- p % 30 = 29 
      rw [h7] 
      norm_num