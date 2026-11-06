import Mathlib

theorem algebra_212757 {a d : ℤ} (h₀ : ∑ i ∈ Finset.range 10, (a + d * i) = 100)
    (h₁ : ∑ i ∈ Finset.range 100, (a + d * i) = 10) :
    ∑ i ∈ Finset.range 110, (a + d * i) = -110 := by
  norm_num [Finset.sum_range_succ] at h₀ h₁ ⊢
  omega