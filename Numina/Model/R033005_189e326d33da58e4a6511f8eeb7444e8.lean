import Mathlib

theorem number_theory_217202 (n : ℕ) : 6 ∣ 17^n - 11^n := by
  have h1 : ∀ (n : ℕ), (17 ^ n : ℕ) % 2 = 1 := by
    intro n
    induction n with
    | zero => 
      norm_num 
    | succ n ih =>
      simp [Nat.pow_add, Nat.pow_mul] at ih ⊢ 
      all_goals omega
  have h2 : ∀ (n : ℕ), (11 ^ n : ℕ) % 2 = 1 := by 
    intro n 
    induction n with 
    | zero => 
      norm_num 
    | succ n ih => 
      simp [Nat.pow_add, Nat.pow_mul] at ih ⊢ 
      all_goals omega 
  have h3 : (17 ^ n - 11 ^ n) % 2 = 0 := by 
    have h1' : (17 ^ n : ℕ) % 2 = 1 := h1 n 
    have h2' : (11 ^ n : ℕ) % 2 = 1 := h2 n 
    omega 
  have h4 : ∀ (n : ℕ), (17 ^ n : ℕ) % 3 = (2 ^ n : ℕ) % 3 := by 
    intro n 
    induction n with 
    | zero => 
      norm_num 
    | succ n ih => 
      simp [Nat.pow_add, Nat.pow_mul] at ih ⊢ 
      all_goals omega 
  have h5 : ∀ (n : ℕ), (11 ^ n : ℕ) % 3 = (2 ^ n : ℕ) % 3 := by 
    intro n 
    induction n with 
    | zero => 
      norm_num 
    | succ n ih => 
      simp [Nat.pow_add, Nat.pow_mul] at ih ⊢ 
      all_goals omega 
  have h6 : (17 ^ n - 11 ^ n) % 3 = 0 := by 
    have h3' : (17 ^ n : ℕ) % 3 = (2 ^ n : ℕ) % 3 := h4 n 
    have h4' : (11 ^ n : ℕ) % 3 = (2 ^ n : ℕ) % 3 := h5 n 
    omega 
  omega