import Mathlib

theorem algebra_198383 (a : ℕ → ℝ) (d : ℝ) (h₀ : ∀ n, a n = a 0 + (n - 1) * d)
    (h₁ : ∑ k in Finset.Icc 1 4, a k = 4) (h₂ : ∑ k in Finset.Icc 1 4, ∑ m in Finset.Icc 1 k, a m = 15) :
    a 0 = 5 / 2 ∧ d = -1 := by
  have eq2 : a 1 = a 0 := by 
    specialize h₀ 1 
    norm_num at h₀ 
    linarith 
  have eq2a : a 2 = a 0 + d := by 
    specialize h₀ 2 
    norm_num at h₀ 
    linarith 
  have eq2b : a 3 = a 0 + 2 * d := by 
    specialize h₀ 3 
    norm_num at h₀ 
    linarith 
  have eq2c : a 4 = a 0 + 3 * d := by 
    specialize h₀ 4 
    norm_num at h₀ 
    linarith 
  have eq1 : ∑ k in Finset.Icc 1 4, a k = a 1 + a 2 + a 3 + a 4 := by 
    norm_num [Finset.sum_Icc_succ_top] 
  rw [eq1] at h₁ 
  rw [eq2, eq2a, eq2b, eq2c] at h₁ 
  have eq3 : 4 * a 0 + 6 * d = 4 := by 
    linarith 
  have eq3b : ∑ k in Finset.Icc 1 4, ∑ m in Finset.Icc 1 k, a m = 
    (∑ m in Finset.Icc 1 1, a m) + 
    (∑ m in Finset.Icc 1 2, a m) + 
    (∑ m in Finset.Icc 1 3, a m) + 
    (∑ m in Finset.Icc 1 4, a m) := by 
    norm_num [Finset.sum_Icc_succ_top] 
  rw [eq3b] at h₂ 
  have h51 : ∑ m in Finset.Icc 1 1, a m = a 1 := by 
    norm_num [Finset.sum_Icc_succ_top] 
  have h52 : ∑ m in Finset.Icc 1 2, a m = a 1 + a 2 := by 
    norm_num [Finset.sum_Icc_succ_top] 
  have h53 : ∑ m in Finset.Icc 1 3, a m = a 1 + a 2 + a 3 := by 
    norm_num [Finset.sum_Icc_succ_top] 
  have h54 : ∑ m in Finset.Icc 1 4, a m = a 1 + a 2 + a 3 + a 4 := by 
    norm_num [Finset.sum_Icc_succ_top] 
  rw [h51, h52, h53, h54] at h₂ 
  rw [eq2, eq2a, eq2b, eq2c] at h₂ 
  have eq4 : 10 * a 0 + 10 * d = 15 := by 
    linarith 
  have h7 : a 0 = 5 / 2 := by 
    linarith [eq3, eq4] 
  have h8 : d = -1 := by 
    linarith [eq3, eq4] 
  exact ⟨h7, h8⟩