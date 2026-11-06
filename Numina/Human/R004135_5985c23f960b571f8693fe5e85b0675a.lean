import Mathlib

theorem number_theory_239022 (n : ℕ) (hn : 100000 ≤ n ∧ n ≤ 999999) (h₀ : n % 10 = 5) (h₁ : 5 * 100000 + n / 10 = 4 * n) :
n = 128205 := by
  omega