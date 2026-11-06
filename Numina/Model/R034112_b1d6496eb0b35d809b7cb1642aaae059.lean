import Mathlib 

theorem AIME_Algebra_13680 : {(p, q) : ℕ × ℕ | p.Prime ∧ q.Prime ∧ (2 : ℝ)*p^3 - q^2 = 2*(p+q)^2} = {(3,2)} := by 
  ext ⟨p, q⟩ 
  simp 
  constructor
  · -- Assume p and q are primes and satisfy the equation 
    rintro ⟨h₁, h₂, heq⟩ 
    have eq1 : (2 : ℝ) * (p : ℝ) ^ 3 - (q : ℝ) ^ 2 = 2 * (p + q : ℝ) ^ 2 := by
      linarith 
    have eq2 : (2 : ℤ) * (p : ℤ) ^ 3 - (q : ℤ) ^ 2 = 2 * (p + q : ℤ) ^ 2 := by 
      exact_mod_cast eq1 
    by_cases h3 : p ≤ 7 
    · -- Assume p ≤ 7 
      have h4 : p ≤ 7 := h3 
      have h5 : q ≤ 22 := by 
        nlinarith [sq_nonneg ((p : ℤ) - 3), sq_nonneg ((q : ℤ) - 2), sq_nonneg ((p : ℤ) - (q : ℤ)), h₁, h₂]
      interval_cases p <;> try { 
          norm_num at eq2 h₁ 
          <;> try { 
            interval_cases q <;> norm_num at eq2 h₂ <;> tauto 
          } 
      }
    · -- Assume p > 7 
      have h4 : p > 7 := by 
        omega 
      have h6 : p ≥ 8 := by 
        omega 
      have h9 : p % 2 = 1 := by 
        by_contra h 
        push_neg at h 
        have h10 : p % 2 = 0 := by 
          omega 
        have h11 : p > 2 := by 
          nlinarith 
        have h12 : ¬p.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega) 
        contradiction 
      -- Prove q must be odd 
      have h7_mod2 : q % 2 = 1 := by 
        by_contra h 
        push_neg at h 
        have h8 : q % 2 = 0 := by 
          omega 
        have h10 : q = 2 := by 
          by_cases h0 : q > 2 
          · -- Assume q > 2 
            have h11 : q % 2 = 0 := h8 
            have h12 : ¬q.Prime := by 
              apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega) (by omega) (by omega) 
            contradiction 
          · -- Assume q ≤ 2 
            interval_cases q <;> norm_num at h₂ <;> tauto 
        rw [show (q : ℤ) = 2 by exact_mod_cast h10] at eq2 
        have eq2' : (2 * (p : ℤ) ^ 3 - 2 * (p : ℤ) ^ 2 - 8 * (p : ℤ) - 12 : ℤ) = 0 := by 
          nlinarith 
        have h12 : p ≤ 7 := by 
          nlinarith [sq_nonneg ((p : ℤ) - 3 : ℤ), sq_nonneg ((p : ℤ) ^ 2 - 4), sq_nonneg ((p : ℤ) * (p - 3 : ℤ)), show p ≥ 2 from Nat.Prime.two_le h₁, sq_nonneg ((p: ℤ) - 2 : ℤ)]
        omega 
      -- Now congr in modulo 8 to close the goal
      have h8_mod8 : (2 * (p : ℤ) ^ 3 - (q : ℤ) ^ 2) % 8 = (2 * (p + q : ℤ) ^ 2) % 8 := by 
        omega 
      -- From p, q odd in mod 8.
      have h9_mod8 : (p : ℤ) % 8 = 1 ∨ (p : ℤ) % 8 = 3 ∨ (p : ℤ) % 8 = 5 ∨ (p : ℤ) % 8 = 7 := by 
        omega 
      have h10_mod8 : (q : ℤ) % 8 = 1 ∨ (q : ℤ) % 8 = 3 ∨ (q : ℤ) % 8 = 5 ∨ (q : ℤ) % 8 = 7 := by 
        omega 
      rcases h9_mod8 with (h9m | h9m | h9m | h9m) <;> rcases h10_mod8 with (h10m | h10m | h10m | h10m) <;> simp [Int.add_emod, Int.sub_emod, pow_two, pow_succ, Int.mul_emod, h9m, h10m] at h8_mod8 
      all_goals 
        omega 
  · -- Show that (3, 2) satisfies the equation 
    rintro ⟨rfl, rfl⟩ 
    constructor 
    · norm_num 
    constructor 
    · norm_num 
    · -- Check the equation 
      norm_num