import Mathlib

theorem algebra_184954 {a b c d : ℝ} (ha : a ≠ 0) (h : ∀ n, (∑ i in Finset.range n, (a * i + b)) / (∑ i in Finset.range n, (c * i + d)) = (7 * n + 1) / (4 * n + 27)) :
    (a * 10 + b) / (c * 10 + d) = 4 / 3 := by 
  have eq1 := h 0
  norm_num [Finset.sum_range_zero] at eq1
  all_goals linarith