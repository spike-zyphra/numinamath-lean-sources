import Mathlib

theorem algebra_274391 (d : ℕ → ℝ) (h₀ : ∀ i ∈ Finset.range 101, d i > 0)
    (h₁ : ∃ x, ∀ i ∈ Finset.range 101, d i = x + i * (d 0 - x)) (h₂ : d 0 = 5)
    (h₃ : ∑ i ∈ Finset.range 5, d (75 + i) = ∑ i ∈ Finset.range 6, d (95 + i)) :
    d 100 = 2.5 := by 
  rcases h₁ with ⟨x, hx⟩
  have h₄ : d 0 = 5 := h₂
  have eq0 := hx 0 (by simp)
  simp [h₄] at eq0 
  have hx0 : x = 5 := by linarith
  -- Calculate the sum from 75 to 79
  have eq1 : ∑ i ∈ Finset.range 5, d (75 + i) = 25 := by 
    have eq10 : d 75 = 5 := by 
      specialize hx 75 (by simp)
      simp [hx0, h₄] at hx ⊢ 
      linarith 
    have eq11 : d 76 = 5 := by 
      specialize hx 76 (by simp)
      simp [hx0, h₄] at hx ⊢ 
      linarith 
    have eq12 : d 77 = 5 := by 
      specialize hx 77 (by simp)
      simp [hx0, h₄] at hx ⊢ 
      linarith 
    have eq13 : d 78 = 5 := by 
      specialize hx 78 (by simp)
      simp [hx0, h₄] at hx ⊢ 
      linarith 
    have eq14 : d 79 = 5 := by 
      specialize hx 79 (by simp)
      simp [hx0, h₄] at hx ⊢ 
      linarith 
    simp [Finset.sum_range_succ, eq10, eq11, eq12, eq13, eq14]
    <;> norm_num
  -- Calculate the sum from 95 to 100 
  have eq2 : ∑ i ∈ Finset.range 6, d (95 + i) = 30 := by 
    have eq20 : d 95 = 5 := by 
      specialize hx 95 (by simp)
      simp [hx0, h₄] at hx ⊢ 
      linarith 
    have eq21 : d 96 = 5 := by 
      specialize hx 96 (by simp)
      simp [hx0, h₄] at hx ⊢ 
      linarith 
    have eq22 : d 97 = 5 := by 
      specialize hx 97 (by simp)
      simp [hx0, h₄] at hx ⊢ 
      linarith 
    have eq23 : d 98 = 5 := by 
      specialize hx 98 (by simp)
      simp [hx0, h₄] at hx ⊢ 
      linarith 
    have eq24 : d 99 = 5 := by 
      specialize hx 99 (by simp)
      simp [hx0, h₄] at hx ⊢ 
      linarith 
    have eq25 : d 100 = 5 := by 
      specialize hx 100 (by simp)
      simp [hx0, h₄] at hx ⊢ 
      linarith 
    simp [Finset.sum_range_succ, eq20, eq21, eq22, eq23, eq24, eq25]
    <;> norm_num 
  rw [eq1] at h₃ 
  rw [eq2] at h₃ 
  norm_num at h₃ 
  all_goals try tauto