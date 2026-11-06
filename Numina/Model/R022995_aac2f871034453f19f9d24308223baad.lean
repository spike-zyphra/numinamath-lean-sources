import Mathlib

theorem number_theory_159625 (n : ℕ) (h₀ : n > 0) (h₁ : 2015 ∣ (10 ^ (n + 3) - 1)) :
    n = 14 := by
  have h3 : n + 3 > 3 := by
    omega
  have h4 : (10 ^ (n + 3) - 1 : ℕ) % 5 = 4 := by
    have h5 : ∀ k : ℕ, (10 ^ (k + 3) - 1 : ℕ) % 5 = 4 := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        simp [Nat.pow_add, Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq] at ih ⊢
        all_goals omega
    specialize h5 n
    simpa using h5
  have h6 : (10 ^ (n + 3) - 1 : ℕ) % 5 = 0 := by
    omega
  omega