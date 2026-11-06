import Mathlib

theorem number_theory_112126 (n : ℕ) :
    19 ∣ 26^n - 7^n := by

  have h2 : ∀ (n : ℕ), (26 ^ n : ℕ) % 19 = (7 ^ n : ℕ) % 19 := by
    intro n
    induction n with
    | zero =>
      all_goals 
        norm_num 
    | succ n ih =>
      have h3 : (26 ^ (n + 1) : ℕ) % 19 = (7 ^ (n + 1) : ℕ) % 19 := by 
        have h26 : (26 ^ (n + 1) : ℕ) % 19 = ((26 ^ n) * 26) % 19 := by 
          ring_nf 
        have h7 : (7 ^ (n + 1) : ℕ) % 19 = ((7 ^ n) * 7) % 19 := by 
          ring_nf 
        rw [h26, h7] 
        simp [Nat.mul_mod, ih] at *
        all_goals 
          omega 
      exact h3 
  have h3 : (26 ^ n % 19) = (7 ^ n % 19) := by 
    specialize h2 n 
    omega 
  have h6 : 26 ^ n ≥ 7 ^ n := by 
    have h7 : ∀ (n : ℕ), (26 : ℕ) ^ n ≥ (7 : ℕ) ^ n := by 
      intro n 
      apply Nat.pow_le_pow_of_le_left 
      all_goals 
        norm_num 
    specialize h7 n 
    linarith 
  have h4 : ((26 ^ n - 7 ^ n) : ℕ) % 19 = 0 := by 
    omega 
  exact Nat.dvd_of_mod_eq_zero h4