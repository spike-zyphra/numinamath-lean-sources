import Mathlib

theorem algebra_21421 {a d : ℝ} (h₀ : ∑ i ∈ Finset.range 5, (a + d * i) = 70)
    (h₁ : ∑ i ∈ Finset.range 10, (a + d * i) = 210) :
    a = 42 / 5 := by
  norm_num [Finset.sum_range_succ] at h₀ h₁
  linarith