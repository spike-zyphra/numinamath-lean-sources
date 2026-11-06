import Mathlib

theorem algebra_94978 (n : ℕ) (h₀ : Even n) (h₁ : ∑ i ∈ Finset.range 5, (n + 2 * i) = ∑ i ∈ Finset.range 8, (2 * i + 1) - 4) :
    n = 8 := by 
  norm_num [Finset.sum_range_succ] at h₁
  omega