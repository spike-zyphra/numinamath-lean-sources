import Mathlib

theorem other_71875 (a : ℕ → ℤ)
    (h₀ : a 0 = 1)
    (h₁ : a 1 = 2)
    (h₂ : ∀ n, a (n + 1) = ∑ i in Finset.range (n + 1), a i) :
    a 11 = 1536 := by
  have h3 := h₂ 0
  norm_num [Finset.sum_range_succ] at h3
  linarith [h₀, h₁, h3]