import Mathlib

theorem algebra_19173 (h : ℕ → ℝ)
    (h₀ : h 0 = 16)
    (h₁ : ∀ n, h (n + 1) = h n / 2) :
    h 0 + 2 * ∑ i ∈ Finset.range 5, h (i + 1) = 47 := by
  have h1 : h 1 = h 0 / 2 := h₁ 0
  have h2 : h 2 = h 1 / 2 := h₁ 1
  have h3 : h 3 = h 2 / 2 := h₁ 2
  have h4 : h 4 = h 3 / 2 := h₁ 3
  have h5 : h 5 = h 4 / 2 := h₁ 4
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp [h₀, h1, h2, h3, h4, h5]
  all_goals norm_num