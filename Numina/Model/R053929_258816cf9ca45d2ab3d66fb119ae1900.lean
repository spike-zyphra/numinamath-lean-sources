import Mathlib

theorem algebra_147626 (a : ℕ → ℝ) (h : ∀ n, ∑ i in Finset.range n, a i = n ^ 2 + 3 * n + 4) :
    a 1 + a 3 + a 5 + a 7 + a 9 + a 11 + a 13 + a 15 + a 17 + a 19 + a 21 = 268 := by
  have h0 := h 0
  norm_num [Finset.sum_range_succ] at h0 
  all_goals 
    linarith