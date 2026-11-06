import Mathlib

theorem algebra_112034 (a : ℝ) (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x ^ 2 - 2 * x - abs (x - 1 - a) - abs (x - 2) + 4)
    (h₁ : ∀ x, f x ≥ 0) :
    a ≥ -2 := by
  have h2 := h₁ 1
  rw [h₀ 1] at h2
  norm_num [abs_of_nonneg, abs_of_nonpos] at h2 ⊢
  all_goals 
  cases' abs_cases a with ha ha 
  all_goals
  linarith