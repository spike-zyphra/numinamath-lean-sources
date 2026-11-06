import Mathlib

theorem number_theory_164146 : ∑ k in Finset.range 101, ⌊(2^100 : ℝ) / (2^50 + 2^k)⌋ = 101 * 2^49 - 50 := by
  norm_num [Finset.sum_range_succ, Int.floor_eq_iff]
  <;> try { native_decide }
  <;> try { norm_num }
  <;> try { native_decide }
  <;> try { linarith }
  <;> try { native_decide }