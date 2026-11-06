import Mathlib

theorem number_theory_187665 (s : ℕ → ℝ)
    (h₀ : s 0 = 1)
    (h₁ : s 1 = 1)
    (h₂ : ∀ n > 0, s (2 * n) = s n)
    (h₃ : ∀ n > 0, s (4 * n + 1) = s (2 * n + 1))
    (h₄ : ∀ n > 0, s (4 * n - 1) = s (2 * n - 1) + (s (2 * n - 1))^2 / s (n - 1)) :
    s 1000 = 720 := by 
  have h1 : s 1000 = s 500 := by 
    specialize h₂ 500 (by norm_num)
    norm_num at h₂ ⊢
    linarith
  have h2 : s 500 = s 250 := by 
    specialize h₂ 250 (by norm_num)
    norm_num at h₂ ⊢
    linarith
  have h3 : s 250 = s 125 := by 
    specialize h₂ 125 (by norm_num)
    norm_num at h₂ ⊢
    linarith
  have h4 : s 125 = s 63 := by 
    specialize h₃ 31 (by norm_num)
    norm_num at h₃ ⊢
    linarith
  have h5 : s 63 = s 31 + (s 31)^2 / s 15 := by 
    specialize h₄ 16 (by norm_num)
    norm_num at h₄ ⊢
    linarith
  have h6 : s 31 = s 15 + (s 15)^2 / s 7 := by 
    specialize h₄ 8 (by norm_num)
    norm_num at h₄ ⊢
    linarith
  have h7 : s 15 = s 7 + (s 7)^2 / s 3 := by 
    specialize h₄ 4 (by norm_num)
    norm_num at h₄ ⊢
    linarith
  have h8 : s 7 = s 3 + (s 3)^2 / s 1 := by 
    specialize h₄ 2 (by norm_num)
    norm_num at h₄ ⊢
    linarith
  have h9 : s 3 = s 1 + (s 1)^2 / s 0 := by 
    specialize h₄ 1 (by norm_num)
    norm_num at h₄ ⊢
    linarith
  rw [h₀] at h9
  rw [h₁] at h9
  have h10 : s 3 = 2 := by 
    norm_num at h9 ⊢ 
    linarith
  rw [h10, h₁] at h8
  have h11 : s 7 = 6 := by 
    norm_num at h8 ⊢ 
    linarith
  rw [h11, h10] at h7
  have h12 : s 15 = 24 := by 
    norm_num at h7 ⊢ 
    linarith
  rw [h12, h11] at h6
  have h13 : s 31 = 120 := by 
    norm_num at h6 ⊢ 
    linarith
  rw [h13, h12] at h5
  have h14 : s 63 = 720 := by 
    norm_num at h5 ⊢ 
    linarith
  rw [h14] at h4
  have h15 : s 125 = 720 := by 
    linarith
  rw [h15] at h3
  have h16 : s 250 = 720 := by 
    linarith
  rw [h16] at h2
  have h17 : s 500 = 720 := by 
    linarith
  rw [h17] at h1
  linarith