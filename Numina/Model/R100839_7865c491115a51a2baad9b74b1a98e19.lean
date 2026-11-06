import Mathlib

theorem number_theory_208290 (p : ℕ) (hp : p.Prime) (h : 5 < p) :
    p^2 ≡ 1 [MOD 30] ∨ p^2 ≡ 19 [MOD 30] := by 
  have h1 : p % 2 ≠ 0 := by 
    by_contra h2
    have h2 : 2 ∣ p := by omega
    have h3 : ¬ p.Prime := by 
      rw [Nat.not_prime_iff_exists_dvd_lt (by omega)]
      use 2
      simp [h2, h]
      all_goals linarith
    contradiction

  have h2 : p % 3 ≠ 0 := by 
    by_contra h3
    have h3 : 3 ∣ p := by omega
    have h4 : ¬ p.Prime := by 
      rw [Nat.not_prime_iff_exists_dvd_lt (by omega)]
      use 3
      simp [h3, h]
      all_goals linarith
    contradiction
  
  have h3 : p % 5 ≠ 0 := by 
    by_contra h4
    have h4 : 5 ∣ p := by omega
    have h5 : ¬ p.Prime := by 
      rw [Nat.not_prime_iff_exists_dvd_lt (by omega)]
      use 5
      simp [h4, h]
      all_goals linarith
    contradiction
  
  have h4 : p % 2 = 1 := by 
    omega

  have h5 : p % 3 = 1 ∨ p % 3 = 2 := by 
    omega

  have h6 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by 
    omega

  have h7 : p % 2 = 1 := h4

  have h8 : p % 3 = 1 ∨ p % 3 = 2 := h5

  have h9 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := h6

  have h10 : p % 2 = 1 := h7

  have h11 : p ^ 2 % 2 = 1 := by
    simp [Nat.pow_mod, h10]

  have h12 : p ^ 2 % 3 = 1 := by
    cases h8 with
    | inl h3 =>
      simp [Nat.pow_mod, h3]
    | inr h3 =>
      simp [Nat.pow_mod, h3]

  have h13 : p ^ 2 % 5 = 1 ∨ p ^ 2 % 5 = 4 := by
    cases h9 with
    | inl h5 => 
      simp [Nat.pow_mod, h5]
    | inr h9 =>
      cases h9 with
      | inl h5 => 
        simp [Nat.pow_mod, h5]
      | inr h9 =>
        cases h9 with
        | inl h5 => 
          simp [Nat.pow_mod, h5]
        | inr h9 => 
          simp [Nat.pow_mod, h9]

  have h14 : (p^2) % 30 = 1 ∨ (p^2) % 30 = 19 := by 
    omega

  simp [Nat.ModEq] at *
  omega