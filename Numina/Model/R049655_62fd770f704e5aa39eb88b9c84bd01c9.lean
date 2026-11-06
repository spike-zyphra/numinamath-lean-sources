import Mathlib

theorem algebra_309191 {a b : ℕ → ℝ} {h₀ : ∃ d, ∀ n, a n = a 0 + d * n}
    {h₁ : ∃ d, ∀ n, b n = b 0 + d * n} {h₂ : ∀ n, ∑ i in Finset.range n, a i / ∑ i in Finset.range n, b i = (2 * n - 1) / (3 * n + 1)} :
    ∀ n, a n / b n = (4 * n - 3) / (6 * n - 2) := by
  have h3 := h₂ 0
  norm_num [Finset.sum_range_zero] at h3 
  all_goals 
    linarith