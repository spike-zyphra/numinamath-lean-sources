import Mathlib

theorem number_theory_126649 {n : ℕ} (hn : n = 1000) :
    (7^(7^n)) % 10 = 7 ∧ (7^(7^n)) % 100 = 7 := by
  rw [hn]
  constructor
  · -- Show the last digit is 7
    have h1 : (7 ^ (7 ^ 1000)) % 10 = 7 := by
      have h2 : ∀ k : ℕ, (7 ^ (4 * k + 1)) % 10 = 7 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
          omega
      have h3 : ((7 ^ 1000) : ℕ) % 4 = 1 := by
        norm_num [Nat.pow_mod]
      have h4 : ∃ k : ℕ, (7 ^ 1000) = 4 * k + 1 := by
        have : ( (7 ^ 1000) ) % 4 = 1 := h3
        refine' ⟨(7 ^ 1000) / 4, by
          omega
        ⟩
      rcases h4 with ⟨k, h7⟩
      rw [show 7 ^ (7 ^ 1000) = 7 ^ (4 * k + 1) by rw [show 4 * k + 1 = 7 ^ 1000 by omega]]
      apply h2 k
    exact h1
  · -- Show the last two digits are 7
    have h2 : (7 ^ (7 ^ 1000)) % 100 = 7 := by
      have h5 : ∀ k : ℕ, (7 ^ (20 * k + 1)) % 100 = 7 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
          omega
      have h6 : ((7 ^ 1000) : ℕ) % 20 = 1 := by
        norm_num [Nat.pow_mod]
      have h7 : ∃ k : ℕ, (7 ^ 1000) = 20 * k + 1 := by
        have : ( (7 ^ 1000) ) % 20 = 1 := h6
        refine' ⟨(7 ^ 1000) / 20, by 
          omega 
        ⟩
      rcases h7 with ⟨k, h7⟩
      rw [show 7 ^ (7 ^ 1000) = 7 ^ (20 * k + 1) by rw [show 20 * k + 1 = 7 ^ 1000 by omega]]
      apply h5 k
    exact h2