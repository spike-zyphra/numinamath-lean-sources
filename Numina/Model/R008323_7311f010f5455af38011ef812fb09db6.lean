import Mathlib

theorem algebra_13798 : ∑ i ∈ Finset.range 166, ⌊(i * 0.6 + 1 : ℚ)⌋ = 8317 := by
  norm_num [Finset.sum_range_succ, Int.floor_eq_iff]
  <;> try { linarith }