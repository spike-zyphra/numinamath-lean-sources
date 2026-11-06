import Mathlib

theorem number_theory_258290 (n : ℕ) (hn : n > 0) :
    5 ∣ 2^(4 * n + 1) + 3 := by
  have h1 : ∀ n : ℕ, 2 ^ (4 * n + 1) % 5 = 2 := by
    intro n
    induction n with
    | zero =>
      simp
      all_goals norm_num
    | succ n ih =>
      have h2 : 2 ^ (4 * (n + 1) + 1) % 5 = 2 := by
        simp [Nat.pow_succ, Nat.mul_add] at ih ⊢
        all_goals
          omega
      exact h2
  have h2 : (2 ^ (4 * n + 1) + 3) % 5 = 0 := by 
    simp [Nat.add_mod, h1 n]
    all_goals norm_num
  exact Nat.dvd_of_mod_eq_zero h2