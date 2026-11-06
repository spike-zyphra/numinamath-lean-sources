import Mathlib

theorem number_theory_327537 : ∑ i ∈ Finset.range 1001, ⌊(2 ^ i : ℝ) / 3⌋ = (2 ^ 1001 - 2) / 3 - 500 := by
  norm_num [Finset.sum_range_succ]
  <;> try { native_decide }
  <;> try { norm_num }
  <;> try { native_decide }
  <;> try { native_decide }
  <;> try { norm_num }
  <;> try { native_decide }
  <;> try { native_decide }
  <;> try { norm_num }
  <;> try { native_decide }
  <;> try { native_decide }
  <;> try { norm_num }
  <;> try { native_decide }
  <;> try { native_decide }
  <;> try { norm_num }
  <;> try { native_decide }