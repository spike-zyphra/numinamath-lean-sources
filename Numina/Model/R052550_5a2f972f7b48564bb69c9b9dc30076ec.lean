import Mathlib

theorem number_theory_120277 (n m : ℕ) (h₀ : n < 10) (h₁ : m < 10)
    (h₂ : 72 ∣ 32000 + 3500 + 100 * n + 10 * m + 17) :
    n = 2 ∧ m = 6 := by 
  interval_cases n <;> interval_cases m 
  <;> norm_num at h₂ 
  <;> omega