import Mathlib

theorem algebra_287292 (a d : ℚ) (h₀ : a = 2022) (h₁ : ∑ i in Finset.range 20, (a + d * i) = 22) :
    d = -20209 / 95 := by
  rw [h₀] at h₁
  norm_num [Finset.sum_range_succ] at h₁
  linarith