import Mathlib
theorem algebra_608601 (a : ℕ → ℝ) (h0 : a 0 = 3) (h1 : a 1 = 2) (hn : ∀ n : ℕ, a (n + 2) = a (n + 1) + a n) : (∑ n in Finset.range 9, a n / (a (n + 1) * a (n + 2))) = 105 / 212:= by
  norm_num [Finset.sum_range_succ, h0, h1, hn]
  <;> norm_num