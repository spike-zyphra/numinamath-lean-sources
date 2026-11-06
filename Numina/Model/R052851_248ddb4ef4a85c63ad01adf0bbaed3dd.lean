import Mathlib

theorem algebra_81491 (n m : ℕ) (h₀ : n > 0) (h₁ : m > 0)
    (h₂ : ∑ i ∈ Finset.range 20, (i + 1) = 207 + n) (h₃ : ∑ i ∈ Finset.range 20, (i + 1) = 225 - m) :
    n + m = 18 := by
  have h4 : ∑ i in Finset.range 20, (i + 1) = 210 := by
    norm_num [Finset.sum_range_succ]
  rw [h4] at h₂ h₃
  omega