import Mathlib

theorem number_theory_4560
    (a b : ℤ)
    (h₀ : ∃ n, a = 4 * n + 1)
    (h₁ : ∃ n, b = 4 * n + 1) :
    ∃ n, a * b = 4 * n + 1 := by 
  rcases h₀ with ⟨k, hk⟩
  rcases h₁ with ⟨m, hm⟩
  use 4 * k * m + k + m
  rw [hk, hm]
  ring