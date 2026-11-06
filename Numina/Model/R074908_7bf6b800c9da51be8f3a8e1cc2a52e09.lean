import Mathlib

theorem algebra_220892 (a d : ℚ) (h₀ : ∑ i ∈ Finset.range 22, (a + d * i) = 1045)
    (h₁ : ∑ i ∈ Finset.range 22, (a + d * (i + 22)) = 2013) :
    a = 53 / 2 := by 
  norm_num [Finset.sum_range_succ] at h₀ h₁ 
  linarith