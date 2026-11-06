import Mathlib

theorem algebra_300855 (f : ℝ → ℝ) (hf : ∀ x, f x = ∑ i ∈ Finset.range 6, ⌊2 ^ i * x⌋) :
    f 3.14 = 196 := by
  rw [hf]
  norm_num [Finset.sum_range_succ]
  <;> try { ring_nf }
  <;> try { norm_num }