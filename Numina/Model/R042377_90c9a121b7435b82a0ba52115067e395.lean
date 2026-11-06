import Mathlib

theorem algebra_6835 (s : ℕ → ℝ) (h₀ : s 0 = 5) (h₁ : ∀ n, s (n + 1) = s n + 35)
    (h₂ : ∀ n, s (n + 2) = s n + 3 * 5 + 9.50) :
    IsLeast {n | s n ≥ 50} 5 := by

  have h3 := h₂ 0
  have h4 := h₁ 0
  have h5 := h₁ 1

  norm_num [h₀] at h3 h4 h5
  all_goals linarith