import Mathlib

theorem number_theory_173002 (p : ℕ) (hp : Nat.Prime p) (h : Nat.Prime (8 * p ^ 2 + 1)) :
    p = 3 := by
  by_cases h3 : p ≤ 3
  · -- If p ≤ 3, then since p is prime, p can only be 2 or 3
    interval_cases p <;> norm_num at hp h ⊢ <;> try { tauto }
  · -- p > 3
    have h4 : p % 3 = 1 ∨ p % 3 = 2 := by 
      by_contra h'
      push_neg at h'
      have h5 : p % 3 = 0 := by
        omega
      have h6 : p > 3 := by 
        omega
      have h7 : ¬Nat.Prime p := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega
      contradiction
    have h8 : (8 * p ^ 2 + 1) % 3 = 0 := by
      rcases h4 with (h4 | h4)
      · -- p % 3 = 1
        have h9 : p % 3 = 1 := h4
        have h10 : p ^ 2 % 3 = 1 := by 
          simp [Nat.pow_mod, h9]
        omega
      · -- p % 3 = 2
        have h9 : p % 3 = 2 := h4
        have h10 : p ^ 2 % 3 = 1 := by 
          simp [Nat.pow_mod, h9]
        omega
    have h9 : (8 * p ^ 2 + 1) > 3 := by 
      have hp4 : p ≥ 4 := by
        omega 
      nlinarith
    have h10 : ¬Nat.Prime (8 * p ^ 2 + 1) := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (8 * p ^ 2 + 1) by omega)
      all_goals nlinarith
    contradiction