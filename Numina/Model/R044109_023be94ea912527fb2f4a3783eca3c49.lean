import Mathlib

theorem algebra_272289 (a : ℕ → ℝ) (t : ℝ) (h₀ : ∀ n, a n = a 0 * t ^ n)
    (h₁ : ∀ n, ∑ i in Finset.range n, a i > 0) :
    t ∈ Set.Ioo (-1) 0 ∪ Set.Ioi 0 := by
  by_cases h2 : t > 0
  · -- If t > 0, then t is in the right interval
    right
    exact h2
  · -- Assume t ≤ 0
    by_cases h3 : t = 0
    · -- If t = 0
      have h4 := h₁ 0
      simp [Finset.sum_range_zero] at h4
      all_goals linarith
    · -- If t < 0
      have ht : t < 0 := by
        by_contra h
        push_neg at h
        have : t = 0 := by linarith
        tauto
      have h4 := h₁ 1
      simp [Finset.sum_range_succ, h₀ 1] at h4
      have h5 := h₁ 2
      simp [Finset.sum_range_succ, h₀ 1, h₀ 2] at h5
      have h6 : a 0 > 0 := by nlinarith
      have h7 : 1 + t > 0 := by
        nlinarith
      have h8 : t > -1 := by nlinarith
      left
      constructor
      · -- Show -1 < t
        linarith
      · -- Show t < 0
        linarith