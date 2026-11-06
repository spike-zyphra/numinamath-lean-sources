import Mathlib

open Finset Real

theorem algebra_297973 {a : ℕ → ℝ}
    (ha : ∀ k, a k = 2 ^ k / (3 ^ (2 ^ k) + 1)) :
    (∑ i ∈ range 10, a i) / (∏ i ∈ range 10, a i) =
    (3 ^ (2 ^ 10) - 1) / 2 ^ 47 - 1 / 2 ^ 36 := by
  norm_num [sum_range_succ, prod_range_succ, ha]