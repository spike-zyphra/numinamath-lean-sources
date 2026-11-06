import Mathlib

theorem algebra_117277 (a : ℕ → ℤ) (h₀ : a 1 = 1) (h₁ : ∀ n, a (n + 1) = 2 * a n + n ^ 2) :
    ∀ n, a n = 7 * 2 ^ (n - 1) - n ^ 2 - 2 * n - 3 := by 
  intro n
  have h2 := h₁ 0
  norm_num at h2 h₀
  all_goals
    omega