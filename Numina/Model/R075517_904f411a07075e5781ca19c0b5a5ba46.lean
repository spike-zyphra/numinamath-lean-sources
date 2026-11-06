import Mathlib

theorem algebra_142801 (a d : ℚ) (h₀ : ∑ i ∈ Finset.range 100, (a + d * i) = 100)
    (h₁ : ∑ i ∈ Finset.range 100, (a + d * (1000 - i - 1)) = 1000) :
    a = 101 / 200 := by
  norm_num [Finset.sum_range_succ] at h₀ h₁
  linarith