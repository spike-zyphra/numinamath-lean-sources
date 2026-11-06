import Mathlib

theorem number_theory_179051 (n : ℕ) (h₀ : Odd n) : 1947 ∣ (46^n + 296 * 13^n) := by
  rcases h₀ with ⟨k, hk⟩ 
  rw [show n = 2 * k + 1 by omega] 
  have h5 : ∀ k : ℕ, 1947 ∣ (46^(2 * k + 1) + 296 * 13^(2 * k + 1)) := by 
    intro k 
    have h6 : (46^(2 * k + 1) + 296 * 13^(2 * k + 1) : Nat) % 3 = 0 := by
      have h7 : ∀ k : ℕ, (46^(2 * k + 1) + 296 * 13^(2 * k + 1) : Nat) % 3 = 0 := by
        intro k
        induction k with 
        | zero =>
          norm_num 
        | succ k ih =>
          simp [Nat.pow_add, Nat.pow_mul, Nat.add_mod, Nat.mul_mod] at ih ⊢
          all_goals norm_num at ih ⊢ 
          all_goals omega 
      specialize h7 k 
      simpa using h7 
    have h7 : (46^(2 * k + 1) + 296 * 13^(2 * k + 1) : Nat) % 11 = 0 := by
      have h8 : ∀ k : ℕ, (46^(2 * k + 1) + 296 * 13^(2 * k + 1) : Nat) % 11 = 0 := by
        intro k 
        induction k with 
        | zero =>
          norm_num 
        | succ k ih =>
          simp [Nat.pow_add, Nat.pow_mul, Nat.add_mod, Nat.mul_mod] at ih ⊢
          all_goals norm_num at ih ⊢
          all_goals omega 
      specialize h8 k 
      simpa using h8 
    have h8 : (46^(2 * k + 1) + 296 * 13^(2 * k + 1) : Nat) % 59 = 0 := by
      have h9 : ∀ k : ℕ, (46^(2 * k + 1) + 296 * 13^(2 * k + 1) : Nat) % 59 = 0 := by
        intro k 
        induction k with 
        | zero =>
          norm_num 
        | succ k ih =>
          simp [Nat.pow_add, Nat.pow_mul, Nat.add_mod, Nat.mul_mod] at ih ⊢
          all_goals norm_num at ih ⊢ 
          all_goals omega 
      specialize h9 k 
      simpa using h9 
    omega 
  specialize h5 k 
  simpa using h5