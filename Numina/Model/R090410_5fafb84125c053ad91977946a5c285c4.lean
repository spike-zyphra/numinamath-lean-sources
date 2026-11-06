import Mathlib

theorem number_theory_240389 (n m : ℕ) (h₀ : n % 3 = 1) (h₁ : m % 3 = 1) :
    (n * m) % 3 = 1 := by
  calc
    (n * m) % 3 = (n % 3) * (m % 3) % 3 := by rw [Nat.mul_mod]
    _ = 1 * 1 % 3 := by rw [h₀, h₁]
    _ = 1 := by norm_num