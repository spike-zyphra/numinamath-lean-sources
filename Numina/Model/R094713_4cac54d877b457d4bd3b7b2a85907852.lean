import Mathlib

open Finset Real

theorem algebra_289064 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 2 / (1 + x ^ 2)) :
    ∑ i ∈ range 2015, f (i + 1) + ∑ i ∈ range 2015, f (1 / (i + 1)) = 2015 := by
  norm_num [sum_range_succ, hf]
  <;> ring_nf <;> norm_num