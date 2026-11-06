import Mathlib

theorem number_theory_257550 (n : ℕ) (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : ∃ k, (10 * (n % 10) + (n / 10)) + n = k ^ 2) :
    (10 * (n % 10) + (n / 10)) + n = 121 := by 
  rcases h₂ with ⟨k, hk⟩

  have h3 : k ^ 2 < 200 := by 
    have h4 : (10 * (n % 10) + (n / 10)) + n < 200 := by 
      interval_cases n <;> omega
    linarith

  have h4 : k ≤ 14 := by nlinarith

  interval_cases k <;> try { 
    omega
  }
  all_goals
    omega