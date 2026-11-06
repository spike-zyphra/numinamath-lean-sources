import Mathlib

theorem number_theory_275547 (n m : ℕ) (h₀ : n % 3 = 1) (h₁ : m % 3 = 1) :
    (n * m) % 3 = 1 := by 
  rw [Nat.mul_mod, h₀, h₁]
  all_goals norm_num