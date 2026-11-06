import Mathlib

theorem number_theory_258461 (p : ℕ) (hp : p.Prime ∧ (p + 4).Prime ∧ (p + 8).Prime) :
    p = 3 := by
  rcases hp with ⟨h1, h2, h3⟩
  by_cases h : p ≤ 3
  ·
    interval_cases p <;> norm_num at h1 h2 h3 ⊢ <;> trivial
  ·
    push_neg at h
    -- Assume p > 3, then we need to show contradiction.
    
    -- Show that p ≡ 1 or 2 (mod 3)
    have h4 : p % 3 = 1 ∨ p % 3 = 2 := by
      by_contra h
      push_neg at h
      have h5 : p % 3 = 0 := by 
        omega
      have h6 : 3 ∣ p := by
        omega
      have h7 : ¬ p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt h6
        all_goals linarith
      contradiction
      
    cases h4 with
    | inl h4 =>
    
      -- If p ≡ 1 (mod 3)
      have h5 : (p + 8) % 3 = 0 := by
        omega
      have h6 : ¬ (p + 8).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 8) by omega)
        all_goals
          omega
      contradiction
      
    | inr h4 =>
      -- If p ≡ 2 (mod 3)
      have h5 : (p + 4) % 3 = 0 := by
        omega
      have h6 : ¬ (p + 4).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 4) by omega)
        all_goals
          omega
      contradiction