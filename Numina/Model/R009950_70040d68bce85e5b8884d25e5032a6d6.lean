import Mathlib

theorem algebra_21843 (x : ℤ) (h : ∃ d, x = 3^2 + d ∧ x = 3^4 - d) : x = 45 := by
  rcases h with ⟨d, h1, h2⟩
  omega