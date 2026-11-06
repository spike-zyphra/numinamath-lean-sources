import Mathlib

open Real

theorem calculus_91716 
    (f : ℝ → ℝ)
    (hf : ∀ x, f x = x ^ 2 / (1 + x ^ 2)) :
    (∑ i ∈ Finset.range 2000, f ((i + 1) / 2000)) + (∑ i ∈ Finset.range 1999, f (2000 / (i + 1))) = 1999.5 := by

  norm_num [Finset.sum_range_succ, hf]
  <;> ring_nf