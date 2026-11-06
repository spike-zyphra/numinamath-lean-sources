import Mathlib

theorem algebra_250002 {a b : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∃ d, ∀ n, b n = b 0 + d * n) (h : ∀ n, (∑ i in Finset.range n, a i) / (∑ i in Finset.range n, b i) = (5 * n - 3) / (n + 9)) :
    a 8 / b 8 = 3 := by 
  have h1 := h 1
  have h0 := h 0 
  norm_num [Finset.sum_range_succ] at h0 h1 
  all_goals 
    linarith