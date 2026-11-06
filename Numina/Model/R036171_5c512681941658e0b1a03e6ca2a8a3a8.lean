import Mathlib

theorem number_theory_884 (p : ℕ) (hp₀ : 5 ≤ p) : ((p.Prime ∧ (p + 2).Prime) → 6 ∣ (p + 1)) ∧ (p.Prime → 24 ∣ (p ^ 2 - 1)) := by 
  constructor 
  · -- Assume both p and p+2 are prime, then p+1 is divisible by 6.
    rintro ⟨hp, hp2⟩
    have h1 : p % 2 = 1 := by
      by_contra h 
      push_neg at h 
      have h2 : p % 2 = 0 := by omega 
      have h3 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
        all_goals linarith 
      tauto 
    -- Prove that p % 3 = 1 or p % 3 = 2
    have h2 : p % 3 = 1 ∨ p % 3 = 2 := by
      by_contra h 
      push_neg at h 
      have h3 : p % 3 = 0 := by omega 
      have h4 : 3 ∣ p := by omega 
      have h5 : ¬p.Prime := by 
        apply Nat.not_prime_of_dvd_of_lt h4
        all_goals 
          omega 
      tauto 
    -- Prove that p % 3 = 2 using the primality of p + 2.
    have h3 : p % 3 = 2 := by
      have hp2' : (p + 2).Prime := hp2 
      by_cases h' : p % 3 = 1 
      · -- Assume p ≡ 1 (mod 3), so p + 2 ≡ 0 (mod 3)
        have h4 : (p + 2) % 3 = 0 := by
          omega 
        have h5 : 3 ∣ (p + 2) := by 
          omega 
        have h6 : ¬(p + 2).Prime := by 
          apply Nat.not_prime_of_dvd_of_lt h5 
          all_goals 
            omega 
        contradiction 
      · -- Assume not p ≡ 1 (mod 3)
        have h7 : p % 3 = 2 := by 
          omega 
        exact h7 
    -- Prove that p + 1 is divisible by 6.
    have h4 : (p + 1) % 2 = 0 := by 
      omega 
    have h5 : (p + 1) % 3 = 0 := by 
      omega 
    omega 
  · -- Assume p is a prime, show that p^2 - 1 is divisible by 24.
    intro hp
    have h1 : p % 2 = 1 := by 
      by_contra h 
      push_neg at h 
      have : ¬p.Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) 
        all_goals 
          omega 
      contradiction 
    -- Prove that p is congruent to 1, 2 modulo 3.
    have h2 : p % 3 = 1 ∨ p % 3 = 2 := by 
      by_contra h 
      push_neg at h 
      have : p % 3 = 0 := by 
        omega 
      have h3 : 3 ∣ p := by 
        omega 
      have : ¬p.Prime := by 
        apply Nat.not_prime_of_dvd_of_lt h3 
        all_goals 
          omega 
      contradiction 
    -- Prove divisibility by 8 and 3.
    have h3 : (p ^ 2) % 8 = 1 := by 
      have h4 : p % 2 = 1 := h1 
      have : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by 
        omega 
      rcases this with (h | h | h | h) <;> simp [h, Nat.pow_mod] 
    have h4 : (p ^ 2) % 3 = 1 := by 
      rcases h2 with (h | h) 
      · 
        simp [h, Nat.pow_mod] 
      · 
        simp [h, Nat.pow_mod] 
    -- Prove divisibility by 24.
    have h5 : (p ^ 2 - 1) % 8 = 0 := by 
      omega 
    have h6 : (p ^ 2 - 1) % 3 = 0 := by 
      omega 
    omega