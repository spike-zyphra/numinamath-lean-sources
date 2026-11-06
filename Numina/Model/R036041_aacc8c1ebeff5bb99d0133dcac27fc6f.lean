import Mathlib

theorem number_theory_257574 (n : ℕ) :
    65 ∣ 7^(4*n) - 4^(4*n) := by
  have h1 : 7 ^ (4 * n) % 5 = 1 := by 
    have h2 : ∀ n : ℕ, 7 ^ (4 * n) % 5 = 1 := by 
      intro n
      induction n with 
      | zero =>
        norm_num
      | succ n ih =>
        simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
        all_goals 
        omega
    exact h2 n
  have h2 : 4 ^ (4 * n) % 5 = 1 := by 
    have h3 : ∀ n : ℕ, 4 ^ (4 * n) % 5 = 1 := by 
      intro n
      induction n with 
      | zero =>
        norm_num
      | succ n ih =>
        simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
        all_goals 
        omega
    exact h3 n
  have h3 : 7 ^ (4 * n) % 13 = (9 : ℕ) ^ n % 13 := by 
    have h4 : ∀ n : ℕ, 7 ^ (4 * n) % 13 = (9 : ℕ) ^ n % 13 := by 
      intro n
      induction n with 
      | zero =>
        norm_num
      | succ n ih =>
        simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
        all_goals 
        omega 
    exact h4 n
  have h4 : 4 ^ (4 * n) % 13 = (9 : ℕ) ^ n % 13 := by 
    have h5 : ∀ n : ℕ, 4 ^ (4 * n) % 13 = (9 : ℕ) ^ n % 13 := by 
      intro n
      induction n with 
      | zero =>
        norm_num
      | succ n ih =>
        simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
        all_goals 
        omega 
    exact h5 n
  have h5 : (7 ^ (4 * n) - 4 ^ (4 * n) : ℕ) % 5 = 0 := by 
    omega
  have h6 : (7 ^ (4 * n) - 4 ^ (4 * n) : ℕ) % 13 = 0 := by 
    omega
  omega