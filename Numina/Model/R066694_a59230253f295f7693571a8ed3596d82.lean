import Mathlib

theorem number_theory_168061 (a : ℕ → ℕ) (h₀ : ∀ n, a n = ∑ i in Finset.range n, a i)
    (h₁ : a 0 = 1) (h₂ : a 1 = 2) :
    a 2021 % 7 = 3 := by
  have h3 := h₀ 0 
  simp [Finset.sum_range_zero] at h3
  omega