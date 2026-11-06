import Mathlib

theorem number_theory_131599 (f : ℕ → ℕ)
    (h₀ : f 0 = 0)
    (h₁ : f 1 = 1)
    (h₂ : ∀ n, f (n + 2) = ∑ i in Finset.range (n + 2), f i) :
    f 14 = 4096 := by
  have f2 : f 2 = 1 := by 
    specialize h₂ 0 
    norm_num [Finset.sum_range_succ, h₀, h₁] at h₂ 
    linarith 
  have f3 : f 3 = 2 := by 
    specialize h₂ 1 
    norm_num [Finset.sum_range_succ, h₀, h₁, f2] at h₂ 
    linarith
  have f4 : f 4 = 4 := by 
    specialize h₂ 2 
    norm_num [Finset.sum_range_succ, h₀, h₁, f2, f3] at h₂ 
    linarith
  have f5 : f 5 = 8 := by 
    specialize h₂ 3 
    norm_num [Finset.sum_range_succ, h₀, h₁, f2, f3, f4] at h₂ 
    linarith
  have f6 : f 6 = 16 := by 
    specialize h₂ 4 
    norm_num [Finset.sum_range_succ, h₀, h₁, f2, f3, f4, f5] at h₂ 
    linarith
  have f7 : f 7 = 32 := by 
    specialize h₂ 5 
    norm_num [Finset.sum_range_succ, h₀, h₁, f2, f3, f4, f5, f6] at h₂ 
    linarith
  have f8 : f 8 = 64 := by 
    specialize h₂ 6 
    norm_num [Finset.sum_range_succ, h₀, h₁, f2, f3, f4, f5, f6, f7] at h₂ 
    linarith
  have f9 : f 9 = 128 := by 
    specialize h₂ 7 
    norm_num [Finset.sum_range_succ, h₀, h₁, f2, f3, f4, f5, f6, f7, f8] at h₂ 
    linarith
  have f10 : f 10 = 256 := by 
    specialize h₂ 8 
    norm_num [Finset.sum_range_succ, h₀, h₁, f2, f3, f4, f5, f6, f7, f8, f9] at h₂ 
    linarith
  have f11 : f 11 = 512 := by 
    specialize h₂ 9 
    norm_num [Finset.sum_range_succ, h₀, h₁, f2, f3, f4, f5, f6, f7, f8, f9, f10] at h₂ 
    linarith
  have f12 : f 12 = 1024 := by 
    specialize h₂ 10 
    norm_num [Finset.sum_range_succ, h₀, h₁, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11] at h₂ 
    linarith
  have f13 : f 13 = 2048 := by 
    specialize h₂ 11 
    norm_num [Finset.sum_range_succ, h₀, h₁, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12] at h₂ 
    linarith
  have f14 : f 14 = 4096 := by 
    specialize h₂ 12 
    norm_num [Finset.sum_range_succ, h₀, h₁, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13] at h₂ 
    linarith
  exact f14