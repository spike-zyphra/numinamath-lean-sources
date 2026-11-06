import Mathlib

theorem number_theory_97496 (a b : ℕ) (ha : Odd a) (hb : Odd b)
    (c : ℕ) (hc : c > 0) :
    Odd (3 ^ a + (b - 1) ^ 2 * c) := by
  have h1 : 3 ^ a % 2 = 1 := by
    have h3 : a % 2 = 1 := by
      obtain ⟨k, hk⟩ := ha
      omega
    have h4 : ∃ k : ℕ, a = 2 * k + 1 := by 
      refine' ⟨(a - 1) / 2, by
        omega 
      ⟩
    rcases h4 with ⟨k, hk⟩
    rw [hk]
    have h5 : ∀ (k : ℕ), 3 ^ (2 * k + 1) % 2 = 1 := by
      intro k
      induction k with
      | zero => 
        norm_num
      | succ k ih =>
        simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
        all_goals 
          omega
    specialize h5 k
    simpa using h5

  -- Show that (b-1) ^2 *c is even
  have h2 : (b - 1) ^ 2 * c % 2 = 0 := by 
    -- Since b is odd, b-1 is even
    have h3 : (b - 1) % 2 = 0 := by
      obtain ⟨k, hk⟩ := hb
      omega
    -- Then (b-1) ^2 is divisible by 4, so divisible by 2
    have h4 : (b - 1) ^ 2 % 2 = 0 := by
      simp [Nat.pow_mod, h3]
    -- Then product is divisible by 2
    simp [Nat.mul_mod, h4]
  
  -- Show that the sum is odd
  have h3 : (3 ^ a + (b - 1) ^ 2 * c) % 2 = 1 := by
    omega

  -- Convert this to the required odd definition
  have h4 : Odd (3 ^ a + (b - 1) ^ 2 * c) := by
    refine' ⟨(3 ^ a + (b - 1) ^ 2 * c) / 2, by 
      omega 
    ⟩
  exact h4