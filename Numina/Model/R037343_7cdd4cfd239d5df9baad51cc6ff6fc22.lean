import Mathlib

theorem number_theory_604738 :
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧ ¬Nat.Prime ((n ^ n) + (n + 1) ^ (n + 1)) := by

  intro N
  use 6 * (N + 1) + 4

  constructor

  . -- Show that n > N
    omega

  .
    let n := 6 * (N + 1) + 4
    have h₁ : n % 6 = 4 := by
      omega
    have h₂ : n % 2 = 0 := by
      omega
    have h₃ : n % 3 = 1 := by
      omega
    have h₄ : (n ^ n) % 3 = 1 := by
      have h₅ : ∀ (k : ℕ), (n ^ k) % 3 = 1 := by
        intro k
        induction k with
        | zero =>
          simp
        | succ k ih =>
          simp [Nat.pow_succ, h₃, Nat.mul_mod, ih]
      specialize h₅ n
      simpa using h₅
    have h₆ : (n + 1) % 3 = 2 := by 
      omega
    have h₇ : ((n + 1) ^ (n + 1)) % 3 = (2 ^ (n + 1)) % 3 := by
      have h₈ : ∀ (k : ℕ), (n + 1) ^ k % 3 = 2 ^ k % 3 := by
        intro k
        induction k with
        | zero =>
          simp
        | succ k ih =>
          simp [Nat.pow_succ, h₆, Nat.mul_mod, ih]
      specialize h₈ (n + 1)
      simpa using h₈
    have h₈ : (2 ^ (n + 1)) % 3 = 2 := by
      have h₉ : n % 2 = 0 := h₂
      have h₁₀ : (n + 1) % 2 = 1 := by 
        omega
      have h₁₂ : ∀ k, (2 : ℕ) ^ (2 * k + 1) % 3 = 2 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [pow_mul, pow_add, pow_two, Nat.mul_mod] at ih ⊢
          all_goals try omega
      have h₁₃ : ∃ k, n + 1 = 2 * k + 1 := by
        refine' ⟨(n + 1) / 2, by omega⟩
      rcases h₁₃ with ⟨k, hk⟩
      rw [show n + 1 = 2 * k + 1 by linarith] 
      apply h₁₂ k
    have h₇ : (n ^ n + (n + 1) ^ (n + 1)) % 3 = 0 := by
      omega
    by_contra h
    have h₉ : Nat.Prime (n ^ n + (n + 1) ^ (n + 1)) := h
    -- Show that the sum is greater than 3
    have h₁₀ : (n ^ n + (n + 1) ^ (n + 1)) > 3 := by
      have h₁₁ : n ≥ 4 := by
        omega
      have h₁₂ : n ^ n ≥ 4 ^ 4 := by
        have h₁₃ : n ≥ 4 := h₁₁
        have h₁₄ : n ^ n ≥ 4 ^ 4 := by
          have h₁₃ : n ≥ 4 := h₁₁
          have h₁₅ : n ^ n ≥ n ^ 4 := by
            have : n ≥ 4 := h₁₃
            exact Nat.pow_le_pow_of_le_right (by omega) h₁₃
          have h₁₆ : n ^ 4 ≥ 4 ^ 4 := by
            have h₁₇ : n ≥ 4 := h₁₃
            exact Nat.pow_le_pow_of_le_left h₁₇ 4
          linarith [h₁₅, h₁₆]
        linarith
      have h₁₃ : (n + 1) ^ (n + 1) ≥ 5 ^ 5 := by
        have h₁₆ : n + 1 ≥ 5 := by
          omega
        have h₁₇ : (n + 1) ^ (n + 1) ≥ 5 ^ 5 := by
          have h₁₆ : n + 1 ≥ 5 := by
            omega
          have h₁₈ : (n + 1) ^ (n + 1) ≥ 5 ^ 5 := by
            have h₁₆ : n + 1 ≥ 5 := by
              omega
            have h₁₉ : n + 1 ≥ 5 := h₁₆
            have h₂₀ : (n + 1) ^ (n + 1) ≥ (n + 1) ^ 5 := by
              have h₂₁ : n + 1 ≥ 5 := h₁₆
              apply Nat.pow_le_pow_of_le_right
              all_goals omega
            have h₂₃ : (n + 1) ^ 5 ≥ 5 ^ 5 := by
              have h₂₅ : n + 1 ≥ 5 := h₁₆
              exact Nat.pow_le_pow_of_le_left h₂₅ 5
            linarith [h₂₀, h₂₃]
          linarith
        linarith
      linarith [h₁₂, h₁₃]
    have h₁₁ : (n ^ n + (n + 1) ^ (n + 1)) % 3 = 0 := h₇
    have h₁₂ : ¬Nat.Prime (n ^ n + (n + 1) ^ (n + 1)) := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (n ^ n + (n + 1) ^ (n + 1)) by omega)
      all_goals linarith
    contradiction