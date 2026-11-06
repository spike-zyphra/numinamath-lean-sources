import Mathlib

theorem algebra_94115 (a : ℕ → ℝ) (h₀ : a 1 = 19) (h₁ : a 9 = 99)
    (h₂ : ∀ n ≥ 3, a n = (∑ i in Finset.Icc 1 (n - 1), a i) / (n - 1)) :
    a 2 = 179 := by

  have h3 : a 3 = (a 1 + a 2) / 2 := by
    specialize h₂ 3 (by norm_num)
    norm_num [Finset.sum_Icc_succ_top, h₀] at h₂
    linarith

  have h4 : a 4 = (a 1 + a 2) / 2 := by
    specialize h₂ 4 (by norm_num)
    norm_num [Finset.sum_Icc_succ_top, h₀, h3] at h₂
    linarith

  have h5 : a 5 = (a 1 + a 2) / 2 := by
    specialize h₂ 5 (by norm_num)
    norm_num [Finset.sum_Icc_succ_top, h₀, h3, h4] at h₂
    linarith

  have h6 : a 6 = (a 1 + a 2) / 2 := by
    specialize h₂ 6 (by norm_num)
    norm_num [Finset.sum_Icc_succ_top, h₀, h3, h4, h5] at h₂
    linarith

  have h7 : a 7 = (a 1 + a 2) / 2 := by
    specialize h₂ 7 (by norm_num)
    norm_num [Finset.sum_Icc_succ_top, h₀, h3, h4, h5, h6] at h₂
    linarith

  have h8 : a 8 = (a 1 + a 2) / 2 := by
    specialize h₂ 8 (by norm_num)
    norm_num [Finset.sum_Icc_succ_top, h₀, h3, h4, h5, h6, h7] at h₂
    linarith

  have h9 : a 9 = (∑ i in Finset.Icc 1 8, a i) / (8 : ℝ) := by
    specialize h₂ 9 (by norm_num)
    norm_num at h₂ ⊢
    try { all_goals linarith }
    all_goals tauto
  
  rw [h9] at h₁
  norm_num [Finset.sum_Icc_succ_top, h₀, h3, h4, h5, h6, h7, h8] at h₁ 
  <;> norm_num at h₁ <;> linarith