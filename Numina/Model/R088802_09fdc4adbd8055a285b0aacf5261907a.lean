import Mathlib

theorem number_theory_182880 (n : ℕ) (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : 72 ∣ (201700 + n)) :
    n = 44 := by 
  interval_cases n <;> omega