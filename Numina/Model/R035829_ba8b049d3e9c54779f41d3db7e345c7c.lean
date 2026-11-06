import Mathlib

theorem number_theory_267577 (n : ℕ) (hn : n > 0) : 7 ∣ 3^(2*n+2) - 2^(n+1) := by

  have h : ∀ (n : ℕ), n > 0 → (3 ^ (2 * n + 2) : ℕ) % 7 = (2 ^ (n + 1) : ℕ) % 7 := by
    intro n hn
    induction n with 
    | zero => 
      exfalso 
      exact Nat.lt_irrefl 0 hn
    | succ n ih =>
      cases n with 
      | zero => 
        simp
      | succ m => 
        simp [Nat.pow_succ, Nat.pow_mul, Nat.pow_add, Nat.mul_mod] at ih ⊢
        all_goals omega
  
  have h2 : n > 0 → 7 ∣ 3 ^ (2 * n + 2) - 2 ^ (n + 1) := by
    intro hn
    have h3 : (3 ^ (2 * n + 2) : ℕ) % 7 = (2 ^ (n + 1) : ℕ) % 7 := h n hn
    have h4 : 7 ∣ 3 ^ (2 * n + 2) - 2 ^ (n + 1) := by
      omega
    exact h4

  exact h2 hn