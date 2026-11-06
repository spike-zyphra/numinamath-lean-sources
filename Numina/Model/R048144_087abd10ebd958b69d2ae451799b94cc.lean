import Mathlib

theorem number_theory_259662 (n : ℕ) (h₀ : n < 1000 ∧ 100 ≤ n) (h₁ : ∃ k, 7 * n = 1000 * k + 638) :
    n = 234 := by 
  rcases h₁ with ⟨k, hk⟩
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  omega