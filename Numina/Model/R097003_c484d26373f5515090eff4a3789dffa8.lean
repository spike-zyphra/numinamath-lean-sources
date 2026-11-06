import Mathlib

theorem number_theory_202572 : ∑ i ∈ Finset.range 1001, ⌊(2 ^ i : ℝ) / 3⌋ = (2 ^ 1001 - 2) / 3 - 500 := by
  norm_num [Finset.sum_range_succ, Int.floor_eq_iff]
  <;> ring_nf
  <;> norm_num
  <;> linarith