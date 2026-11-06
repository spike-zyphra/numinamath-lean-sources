import Mathlib

open scoped BigOperators

theorem algebra_468
  (a : ℕ → ℝ)
  (h₀ : a 0 = 10)
  (h₁ : a 1 = 20)
  (h₂ : ∀ n, a (n + 1) = (∑ i in Finset.range ((n + 1) + 1), a i) / (n + 2)) :
  a 2010 = 15 := by
    have h3 := h₂ 0
    norm_num [Finset.sum_range_succ] at h3
    linarith [h₀, h₁, h3]