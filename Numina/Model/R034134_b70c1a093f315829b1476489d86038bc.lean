import Mathlib

theorem number_theory_224691 (n m : ℕ) (h₀ : n < m) (h₁ : n > 0) (h₂ : m > 0)
    (h₃ : n = 133 ∨ n = 134 ∨ n = 59 ∨ n = 60) :
    n = 59 ∨ n = 60 ∨ n = 133 ∨ n = 134 := by
  rcases h₃ with (rfl | rfl | rfl | rfl)
  · -- Case where n = 133
    simp
  · -- Case where n = 134
    simp
  · -- Case where n = 59
    simp
  · -- Case where n = 60
    simp