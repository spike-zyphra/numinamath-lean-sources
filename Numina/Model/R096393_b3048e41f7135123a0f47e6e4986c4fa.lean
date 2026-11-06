import Mathlib

theorem number_theory_244445 (n : ℕ) : 13 ∣ 7^(2*n) + 10^(n+1) + 2*10^n := by 
  have h1 : ∀ n : ℕ, 13 ∣ 7^(2*n) + 10^(n+1) + 2*10^n := by 
    intro n 
    induction n with
    | zero =>
      use 1
      all_goals 
        norm_num 
    | succ n ih =>
      have eq : 7 ^ (2 * (n + 1)) + 10 ^ ((n + 1) + 1) + 2 * 10 ^ (n + 1) = 
        49 * 7 ^ (2 * n) + 10 * 10 ^ (n + 1) + 2 * 10 ^ (n + 1) := by 
          ring_nf 
      rw [eq]
      omega
  exact h1 n