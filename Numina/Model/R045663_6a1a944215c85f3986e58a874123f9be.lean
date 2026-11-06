import Mathlib

theorem number_theory_305149 (a : ℕ → ℝ)
    (h₀ : a 1 = 1)
    (h₁ : a 2 = 7)
    (h₂ : ∀ n, a (n + 2) = (a (n + 1)^2 - 1) / a n) :
    ∀ n > 0, ∃ m : ℕ, a n = m ∧ 0 < m ∧ ∃ k : ℕ, k^2 = 9 * m * a (n + 1) + 1 := by
  have h3 := h₂ 0
  norm_num [h₀, h₁] at h3
  all_goals linarith