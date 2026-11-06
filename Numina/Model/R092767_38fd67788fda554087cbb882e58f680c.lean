import Mathlib

theorem algebra_288233 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 2 / (x ^ 2 - 100 * x + 5000)) :
    ∑ i ∈ Finset.range 100, f (i + 1) = 101 := by 
  norm_num [Finset.sum_range_succ, hf]