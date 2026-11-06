import Mathlib

theorem number_theory_125253 (n : ℕ) :
    (n ^ 9999 - n ^ 5555) % 10 = 0 := by
  have h1 : n ^ 9999 % 2 = n ^ 5555 % 2 := by
    have h2 : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases h2 with (h2 | h2)
    · -- if n is even
      have h3 : n % 2 = 0 := h2
      have h4 : n ^ 9999 % 2 = 0 := by
        have h5 : n % 2 = 0 := h3
        simp [Nat.pow_mod, h5]
      have h6 : n ^ 5555 % 2 = 0 := by
        have h7 : n % 2 = 0 := h3
        simp [Nat.pow_mod, h7]
      omega
    · -- if n is odd
      have h3 : n % 2 = 1 := h2
      have h4 : n ^ 9999 % 2 = 1 := by
        have h5 : n % 2 = 1 := h3
        simp [Nat.pow_mod, h5]
      have h6 : n ^ 5555 % 2 = 1 := by
        have h7 : n % 2 = 1 := h3
        simp [Nat.pow_mod, h7]
      omega
  have h2 : n ^ 9999 % 5 = n ^ 5555 % 5 := by
    have h3 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
    rcases h3 with (h3 | h3 | h3 | h3 | h3)
    · -- n ≡ 0 [MOD 5]
      simp [Nat.pow_mod, h3]
    · -- n ≡ 1 [MOD 5]
      simp [Nat.pow_mod, h3]
    · -- n ≡ 2 [MOD 5]
      have h4 : n % 5 = 2 := h3
      have h5 : n ^ 9999 % 5 = n ^ 5555 % 5 := by
        have h5'1 : n ^ 9999 % 5 = ((n % 5) ^ 9999) % 5 := by
          simp [Nat.pow_mod]
        have h5'2 : n ^ 5555 % 5 = ((n % 5) ^ 5555) % 5 := by
          simp [Nat.pow_mod]
        rw [h5'1, h5'2, h4]
        all_goals norm_num
      exact h5
    · -- n ≡ 3 [MOD 5]
      have h4 : n % 5 = 3 := h3
      have h5 : n ^ 9999 % 5 = n ^ 5555 % 5 := by
        have h5'1 : n ^ 9999 % 5 = ((n % 5) ^ 9999) % 5 := by
          simp [Nat.pow_mod]
        have h5'2 : n ^ 5555 % 5 = ((n % 5) ^ 5555) % 5 := by
          simp [Nat.pow_mod]
        rw [h5'1, h5'2, h4]
        all_goals norm_num
      exact h5
    · -- n ≡ 4 [MOD 5]
      have h4 : n % 5 = 4 := h3
      have h5 : n ^ 9999 % 5 = n ^ 5555 % 5 := by
        have h5'1 : n ^ 9999 % 5 = ((n % 5) ^ 9999) % 5 := by
          simp [Nat.pow_mod]
        have h5'2 : n ^ 5555 % 5 = ((n % 5) ^ 5555) % 5 := by
          simp [Nat.pow_mod]
        rw [h5'1, h5'2, h4]
        all_goals norm_num
      exact h5
  have h3 : (n ^ 9999 - n ^ 5555) % 2 = 0 := by 
    omega
  have h4 : (n ^ 9999 - n ^ 5555) % 5 = 0 := by 
    omega 
  omega