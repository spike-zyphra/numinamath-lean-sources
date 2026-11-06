import Mathlib

theorem algebra_225399 (a : ℕ → ℝ) (h₀ : a 1 = 19) (h₁ : a 9 = 99)
    (h₂ : ∀ n ≥ 3, a n = (∑ i ∈ Finset.range (n - 1), a (n - 1 - i)) / (n - 1)) :
    a 2 = 179 := by
  have h3 : a 3 = (a 1 + a 2) / 2 := by 
    have h3 := h₂ 3 (by norm_num)
    norm_num [Finset.sum_range_succ] at h3
    linarith
  have h4 : a 4 = (a 1 + a 2) / 2 := by 
    have h4 := h₂ 4 (by norm_num)
    norm_num [Finset.sum_range_succ] at h4
    rw [h3] at h4
    linarith
  have h5 : a 5 = (a 1 + a 2) / 2 := by 
    have h5 := h₂ 5 (by norm_num)
    norm_num [Finset.sum_range_succ] at h5
    rw [h4, h3] at h5
    linarith 
  have h6 : a 6 = (a 1 + a 2) / 2 := by 
    have h6 := h₂ 6 (by norm_num)
    norm_num [Finset.sum_range_succ] at h6
    rw [h5, h4, h3] at h6 
    linarith 
  have h7 : a 7 = (a 1 + a 2) / 2 := by 
    have h7 := h₂ 7 (by norm_num)
    norm_num [Finset.sum_range_succ] at h7
    rw [h6, h5, h4, h3] at h7 
    linarith 
  have h8 : a 8 = (a 1 + a 2) / 2 := by 
    have h8 := h₂ 8 (by norm_num)
    norm_num [Finset.sum_range_succ] at h8
    rw [h7, h6, h5, h4, h3] at h8 
    linarith 
  have h9 : a 9 = (a 1 + a 2) / 2 := by 
    have h9 := h₂ 9 (by norm_num)
    norm_num [Finset.sum_range_succ] at h9 
    rw [h8, h7, h6, h5, h4, h3] at h9 
    linarith 
  rw [h₀] at h9 
  rw [h₁] at h9 
  linarith 
  all_goals norm_num [Finset.sum_range_succ] at *
  all_goals linarith