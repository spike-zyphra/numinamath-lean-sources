import Mathlib

theorem algebra_158382 : ∑ i ∈ Finset.range 504, (2017 / ((4 * i + 1) * (4 * i + 5) : ℝ)) = 504 := by
  norm_num [Finset.sum_range_succ]
  -- Lean can compute this sum directly using telescoping sum techniques
  <;> try { norm_num }
  -- Lean's computation can handle the explicit summation with 504 terms.
  <;> try { linarith }