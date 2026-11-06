import Mathlib

theorem number_theory_210839 : (7^(2016^2017)) % 100 = 1 := by
  have h1 : ∀ k : ℕ, (7 ^ (4 * k)) % 100 = 1 := by
    intro k 
    induction k with 
    | zero => 
      norm_num
    | succ k ih => 
      simp [Nat.pow_succ, Nat.mul_add] at ih ⊢
      all_goals
        norm_num at ih ⊢
        all_goals
          omega
  have h2 : ∃ k : ℕ, 2016 ^ 2017 = 4 * k := by
    use (2016 ^ 2017) / 4
    have h2016 : 2016 % 4 = 0 := by norm_num
    have h2016_pow : (2016 ^ 2017) % 4 = 0 := by
      simp [Nat.pow_mod, h2016]
    omega
  rcases h2 with ⟨k, hk⟩
  rw [hk]
  exact h1 k