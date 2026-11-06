import Mathlib

theorem algebra_195624 (a d : ℕ) (h₀ : a > 0) (h₁ : d > 0)
    (h₂ : a + d = 11) (h₃ : ∑ i ∈ Finset.range 10, (a + d * i) = 320) :
    d = 6 := by
  norm_num [Finset.sum_range_succ] at h₃
  omega