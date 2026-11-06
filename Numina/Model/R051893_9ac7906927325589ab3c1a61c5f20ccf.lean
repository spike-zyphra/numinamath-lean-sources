import Mathlib

theorem algebra_4930 (n : ℤ) (h₀ : Even n) (h₁ : ∑ i ∈ Finset.range 14, (n + 2 * i) = 119 * 14) :
    n = 106 := by
  norm_num [Finset.sum_range_succ] at h₁ 
  linarith