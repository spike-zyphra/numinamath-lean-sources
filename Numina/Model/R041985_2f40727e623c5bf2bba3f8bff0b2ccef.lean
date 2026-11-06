import Mathlib


theorem number_theory_276668 (n : ℕ) (hn : n > 0) :
    IsSquare ((10^n - 1) % 37) := by

  have h1 : ∀ n : ℕ, (10 ^ (3 * n + 1) : ℕ) % 37 = 10 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
      omega

  have h2 : ∀ n : ℕ, (10 ^ (3 * n + 2) : ℕ) % 37 = 26 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
      omega

  have h3 : ∀ n : ℕ, (10 ^ (3 * n) : ℕ) % 37 = 1 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
      omega

  have h4 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega

  rcases h4 with (h4 | h4 | h4)

  · -- n % 3 = 0
    have h5 : ∃ k, n = 3 * k := by 
      refine ⟨n / 3, by omega⟩
    rcases h5 with ⟨k, hk⟩
    have h7 : (10 ^ n) % 37 = 1 := by
      rw [show n = 3 * k by linarith]
      apply h3 k
    have h8 : (10 ^ n - 1) % 37 = 0 := by
      have h9 : (10 ^ n) % 37 = 1 := h7
      have h10 : (10 ^ n) ≥ 1 := by
        have : 10 ^ n ≥ 1 := by
          apply Nat.one_le_pow
          all_goals norm_num
        linarith
      omega
    rw [h8]
    exact ⟨0, by norm_num⟩

  · -- n % 3 = 1
    have h5 : ∃ k, n = 3 * k + 1 := by 
      refine ⟨(n - 1) / 3, by omega⟩
    rcases h5 with ⟨k, hk⟩
    have h7 : (10 ^ n) % 37 = 10 := by
      rw [show n = 3 * k + 1 by linarith]
      apply h1 k
    have h8 : (10 ^ n - 1) % 37 = 9 := by
      have h9 : (10 ^ n) % 37 = 10 := h7
      have h10 : (10 ^ n) ≥ 1 := by
        have : 10 ^ n ≥ 1 := by
          apply Nat.one_le_pow
          all_goals norm_num
        linarith
      omega
    rw [h8]
    exact ⟨3, by norm_num⟩

  · -- n % 3 = 2
    have h5 : ∃ k, n = 3 * k + 2 := by 
      refine ⟨(n - 2) / 3, by omega⟩
    rcases h5 with ⟨k, hk⟩
    have h7 : (10 ^ n) % 37 = 26 := by
      rw [show n = 3 * k + 2 by linarith]
      apply h2 k
    have h8 : (10 ^ n - 1) % 37 = 25 := by
      have h9 : (10 ^ n) % 37 = 26 := h7
      have h10 : (10 ^ n) ≥ 1 := by
        have : 10 ^ n ≥ 1 := by
          apply Nat.one_le_pow
          all_goals norm_num
        linarith
      omega
    rw [h8]
    exact ⟨5, by norm_num⟩