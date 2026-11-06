import Mathlib

theorem number_theory_1657 (n : ℕ) (h₀ : n > 0) (h₁ : 4 * n + 9 = 6 * (n - 1) + x) (h₂ : x < 3) :
    n = 7 ∧ n * 4 + 9 = 37 := by
  -- Assume x is less than 3, derive equations
  have h3 : n ≤ 7 := by
    omega
  have h4 : n > 6 := by 
    omega 
  have hn : n = 7 := by 
    omega
  have ho : n * 4 + 9 = 37 := by 
    nlinarith [hn]
  constructor
  · exact hn
  · exact ho