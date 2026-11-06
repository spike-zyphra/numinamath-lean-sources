import Mathlib

theorem algebra_755 (a : ℕ) (h₀ : a > 0) (h₁ : ∑ i ∈ Finset.range 7, (a + i) = 381) : a + 3 = 24 := by
  norm_num [Finset.sum_range_succ] at h₁
  omega