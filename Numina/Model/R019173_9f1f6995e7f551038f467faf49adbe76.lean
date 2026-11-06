import Mathlib

theorem number_theory_179608 (n : ℕ) (h₀ : n % 10 = 6) (h₁ : 6 * 100000 + n % 100000 = 4 * n) :
    n = 153846 := by
  have h3 : n = 153846 := by
    omega
  exact h3