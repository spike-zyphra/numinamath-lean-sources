import Mathlib

theorem number_theory_232378 (n : ℕ) (h₀ : n % 2 = 0) (h₁ : n % 3 = 0)
    (h₂ : ∃ k, n = 7000 + 10 * k + 7) :
    n = 7026 ∨ n = 7122 ∨ n = 7422 ∨ n = 7626 ∨ n = 7926 := by 
  rcases h₂ with ⟨k, hk⟩
  have h3 : n % 10 = 7 := by
    omega
  have h4 : n % 2 = 1 := by 
    omega
  exfalso
  omega