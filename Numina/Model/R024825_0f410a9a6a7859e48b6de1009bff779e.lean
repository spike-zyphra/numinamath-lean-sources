import Mathlib

theorem number_theory_60028 (n : ℕ) :
    ∃ a b c d : ℕ, 0 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ 2^n = a^2 + b^2 + c^2 + d^2 := by
  by_cases h1 : n % 2 = 0 
  · -- Case 1: n is even
    have h11 : ∃ k, n = 2 * k := by 
      refine' ⟨n / 2, by 
        omega 
      ⟩ 
    rcases h11 with ⟨k, hk⟩ 
    use 0, 0, 0, 2^k 
    constructor 
    · -- Show 0 ≤ a 
      all_goals omega 
    constructor 
    · -- Show a ≤ b 
      all_goals omega 
    constructor 
    · -- Show b ≤ c 
      all_goals omega 
    constructor 
    · -- Show c ≤ d 
      all_goals 
        have h8 : (2^k : ℕ) ≥ 0 := by positivity 
        all_goals omega 
    · -- Show 2^n = a^2 + b^2 + c^2 + d^2 
      rw [show n = 2 * k by omega] 
      have h2 : (2 : ℕ) ^ (2 * k) = (2 ^ k) ^ 2 := by 
        ring_nf 
      nlinarith [h2, sq_nonneg (2 ^ k : ℕ)]
  · -- Case 2: n is odd 
    have h1 : n % 2 = 1 := by 
      omega 
    have h11 : ∃ k, n = 2 * k + 1 := by 
      refine' ⟨n / 2, by 
        omega 
      ⟩ 
    rcases h11 with ⟨k, hk⟩ 
    use 0, 0, 2^k, 2^k 
    constructor 
    · -- Show 0 ≤ a 
      all_goals omega 
    constructor 
    · -- Show a ≤ b 
      all_goals omega 
    constructor 
    · -- Show b ≤ c 
      all_goals 
        have h8 : (2^k : ℕ) ≥ 0 := by positivity 
        all_goals omega 
    constructor 
    · -- Show c ≤ d 
      all_goals 
        have h8 : (2^k : ℕ) ≥ 0 := by positivity 
        all_goals omega 
    · -- Show 2^n = a^2 + b^2 + c^2 + d^2 
      rw [show n = 2 * k + 1 by omega] 
      have h3 : (2 : ℕ) ^ (2 * k + 1) = 2 * ((2 ^ k) ^ 2) := by 
        ring_nf 
      nlinarith [h3, sq_nonneg (2 ^ k : ℕ)]