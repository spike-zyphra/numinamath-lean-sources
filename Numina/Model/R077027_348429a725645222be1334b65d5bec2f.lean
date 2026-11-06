import Mathlib

theorem number_theory_300864 : ∑ i in Finset.range 1001, ⌊(1 / 3 : ℝ) * 2 ^ i⌋ = (2 ^ 1001 - 2) * (1 / 3 : ℝ) - 500 := by
  norm_num [Finset.sum_range_succ, Int.floor_eq_iff]
  <;> ring_nf <;> norm_num