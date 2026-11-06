import Mathlib

open Real

theorem algebra_294943 {a : ℕ → ℝ} (ha : ∀ n, a n = 1 / (2 * n - 1) - 1 / (2 * n + 1)) :
    201 * ∑ i in Finset.range 100, a (i + 1) = 200 := by
  norm_num [Finset.sum_range_succ, ha]
  <;> norm_num
  <;> ring
  <;> norm_num
  <;> ring