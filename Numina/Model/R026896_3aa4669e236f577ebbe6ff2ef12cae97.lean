import Mathlib

open Finset Real

theorem algebra_297068 {f : ℝ → ℝ} (hf : ∀ x, f x = x / (1 + x)) :
    ∑ i ∈ range 2006, f (1 / (i + 1)) + ∑ i ∈ range 2007, f i = 2006 := by
  norm_num [sum_range_succ, hf]
  <;> ring_nf
  <;> norm_num