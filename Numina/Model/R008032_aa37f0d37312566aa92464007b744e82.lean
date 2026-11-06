import Mathlib

open Finset

theorem algebra_142362 {a : ℕ → ℝ} (ha : ∀ k, a k = 2 ^ k / (3 ^ (2 ^ k) + 1)) :
    (∑ i ∈ range 10, a i) / (∏ i ∈ range 10, a i) =
    (3 ^ (2 ^ 10) - 2 ^ 11 - 1) / 2 ^ 47 := by
  norm_num [sum_range_succ, prod_range_succ, ha]
  <;> ring_nf <;> norm_num