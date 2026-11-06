import Mathlib

theorem algebra_12742 {a : ℕ → ℝ} (h : ∀ n, ∑ i in Finset.range n, a i = 2 * n - 1) :
    ∑ i in Finset.range n, (a i) ^ (i + 1) = 2 ^ (n + 1) - 3 := by 
  have h0 := h 0
  norm_num [Finset.sum_range_zero] at h0
  all_goals linarith