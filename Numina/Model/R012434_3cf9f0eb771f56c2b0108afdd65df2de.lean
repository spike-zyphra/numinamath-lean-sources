import Mathlib

theorem algebra_131708 (n : ℕ) (hn : n > 0) (a : ℕ → ℝ)
    (h₀ : ∀ i, i + 6 < n → ∑ j ∈ Finset.range 7, a (i + j) < 0)
    (h₁ : ∀ i, i + 10 < n → ∑ j ∈ Finset.range 11, a (i + j) > 0) :
    n ≤ 16 := by
  by_contra h
  push_neg at h
  have h17 : n ≥ 17 := by linarith
  have h2 := h₀ 0 (by linarith [h17])
  have h3 := h₀ 1 (by linarith [h17])
  have h4 := h₀ 2 (by linarith [h17])
  have h5 := h₀ 3 (by linarith [h17])
  have h6 := h₀ 4 (by linarith [h17])
  have h7 := h₀ 5 (by linarith [h17])
  have h8 := h₀ 6 (by linarith [h17])
  have h9 := h₀ 7 (by linarith [h17])
  have h10 := h₀ 8 (by linarith [h17])
  have h11 := h₀ 9 (by linarith [h17])
  have h12 := h₀ 10 (by linarith [h17])
  -- Apply h₁ to indices 0, 1, 2, 3, 4, 5, 6
  have h13 := h₁ 0 (by linarith [h17])
  have h14 := h₁ 1 (by linarith [h17])
  have h15 := h₁ 2 (by linarith [h17])
  have h16 := h₁ 3 (by linarith [h17])
  have h17_1 := h₁ 4 (by linarith [h17])
  have h18 := h₁ 5 (by linarith [h17])
  have h19 := h₁ 6 (by linarith [h17])
  norm_num [Finset.sum_range_succ] at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17_1 h18 h19
  all_goals linarith