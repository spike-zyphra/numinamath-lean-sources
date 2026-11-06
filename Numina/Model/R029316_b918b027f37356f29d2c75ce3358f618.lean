import Mathlib

theorem algebra_98652 (a d : ℕ) (h₀ : a + 5 * d = 2 * a)
    (h₁ : ∑ i ∈ Finset.range 6, (a + i * d) = 990) : a + 5 * d = 220 := by 
  norm_num [Finset.sum_range_succ] at h₁ 
  omega