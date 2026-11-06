import Mathlib

theorem number_theory_280057 (n : ℕ) :
    7 ∣ 3^(2*n + 2) - 2^(n + 1) := by 
  have h1 : ∀ (n : ℕ), 7 ∣ 3^(2*n + 2) - 2^(n + 1) := by 
    intro n
    have h2 : ∀ (n : ℕ), (3 ^ (2 * n + 2) : ℕ) % 7 = (2 ^ (n + 1) : ℕ) % 7 := by 
      intro n
      induction n with 
      | zero =>
        norm_num
      | succ n ih =>
        simp [Nat.pow_succ, Nat.pow_mul, Nat.add_mod] at ih ⊢
        all_goals 
          omega 
    have h3 : (3 ^ (2 * n + 2) : ℕ) % 7 = (2 ^ (n + 1) : ℕ) % 7 := h2 n 
    have h4 : 7 ∣ 3^(2*n + 2) - 2^(n + 1) := by 
      omega 
    exact h4 
  exact h1 n