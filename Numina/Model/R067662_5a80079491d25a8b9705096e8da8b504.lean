import Mathlib

open Finset Real

theorem algebra_261269 (x : ℕ → ℝ) (hx : ∀ i ∈ range 102, x i = i / 101) :
    ∑ i ∈ range 102, (x i)^3 / (1 - 3 * x i + 3 * (x i)^2) = 51 := by
  norm_num [sum_range_succ, hx]
  <;> try { linarith }