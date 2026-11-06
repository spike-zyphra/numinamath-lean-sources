import Mathlib

theorem algebra_13358 (n : ℕ) (h₀ : n > 0) (h₁ : Even n)
    (H : ∑ i ∈ Finset.range 20, (2 * i + 2) = n + (n + 2) + (n + 4) + (n + 6)) : n + 6 = 108 := by
  norm_num [Finset.sum_range_succ] at H
  omega