import Mathlib

theorem number_theory_182624 (n m : ℕ) (h₀ : Odd n) (h₁ : Odd m) :
    16 ∣ (n ^ 4 - m ^ 4) := by
  have h2 : n % 16 = 1 ∨ n % 16 = 3 ∨ n % 16 = 5 ∨ n % 16 = 7 ∨ n % 16 = 9 ∨ n % 16 = 11 ∨ n % 16 = 13 ∨ n % 16 = 15 := by 
    rcases h₀ with ⟨k, hk⟩
    have : n % 16 = 1 ∨ n % 16 = 3 ∨ n % 16 = 5 ∨ n % 16 = 7 ∨ n % 16 = 9 ∨ n % 16 = 11 ∨ n % 16 = 13 ∨ n % 16 = 15 := by
      omega
    assumption
  have h3 : m % 16 = 1 ∨ m % 16 = 3 ∨ m % 16 = 5 ∨ m % 16 = 7 ∨ m % 16 = 9 ∨ m % 16 = 11 ∨ m % 16 = 13 ∨ m % 16 = 15 := by
    rcases h₁ with ⟨k, hk⟩
    have : m % 16 = 1 ∨ m % 16 = 3 ∨ m % 16 = 5 ∨ m % 16 = 7 ∨ m % 16 = 9 ∨ m % 16 = 11 ∨ m % 16 = 13 ∨ m % 16 = 15 := by
      omega
    assumption
  have h4 : n ^ 4 % 16 = 1 := by
    rcases h2 with (h | h | h | h | h | h | h | h)
    all_goals 
      simp [h, Nat.pow_mod, Nat.mul_mod]
    all_goals omega
  have h5 : m ^ 4 % 16 = 1 := by
    rcases h3 with (h | h | h | h | h | h | h | h)
    all_goals 
      simp [h, Nat.pow_mod, Nat.mul_mod]
    all_goals omega
  have h6 : (n ^ 4 - m ^ 4) % 16 = 0 := by 
    have h7 : n ^ 4 % 16 = 1 := h4
    have h8 : m ^ 4 % 16 = 1 := h5
    omega
  exact Nat.dvd_of_mod_eq_zero h6