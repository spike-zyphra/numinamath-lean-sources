import Mathlib

theorem number_theory_244032 (n : ℕ) (h₀ : n < 9) (h₁ : 43 * n % 2 = 1) (h₂ : 43 * n % 3 = 1)
    (h₃ : 43 * n % 4 = 1) (h₄ : 43 * n % 5 = 1) (h₅ : 43 * n % 6 = 1) :
    n = 7 ∧ 43 * 7 = 301 := by
  have h_n : n = 7 := by
    interval_cases n <;> omega
  constructor
  · exact h_n
  · norm_num