import Mathlib

theorem algebra_104090 (n : ℕ) (h₀ : n > 0) (h₁ : 30 + (n - 1) * 4 = 70) :
    ∑ i ∈ Finset.range n, (30 + i * 4) = 550 := by
  have h2 : n = 11 := by
    have h3 : n > 0 := h₀
    have h4 : n = 11 := by
      omega
    exact h4
  rw [h2]
  norm_num [Finset.sum_range_succ]