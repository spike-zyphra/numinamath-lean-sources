import Mathlib

theorem algebra_275137 {f : ℝ → ℝ} (h : ∀ x, f (x + 2) = 1 / f x) (h' : f 1 = -5) :
    f (f 5) = -1 / 5 := by 

  have hf3 : f (3 : ℝ) = -1 / 5 := by
    have h1 : f (3 : ℝ) = 1 / f (1 : ℝ) := by 
      specialize h (1 : ℝ)
      norm_num at h ⊢ 
      linarith 
    rw [h'] at h1 
    norm_num at h1 ⊢ 
    linarith
  
  have hf5 : f (5 : ℝ) = -5 := by 
    have h2 : f (5 : ℝ) = 1 / f (3 : ℝ) := by 
      specialize h (3 : ℝ)
      norm_num at h ⊢ 
      linarith 
    rw [hf3] at h2 
    norm_num at h2 ⊢ 
    linarith

  have hf55 : f (-5 : ℝ) = -1 / 5 := by
    have h1 : f (-3 : ℝ) = 1 / f (-5 : ℝ) := by
      specialize h (-5 : ℝ)
      norm_num at h ⊢
      linarith
    have h2 : f (-1 : ℝ) = 1 / f (-3 : ℝ) := by
      specialize h (-3 : ℝ)
      norm_num at h ⊢ 
      linarith
    have h3 : f (1 : ℝ) = 1 / f (-1 : ℝ) := by 
      specialize h (-1 : ℝ)
      norm_num at h ⊢
      linarith
    rw [h'] at h3 
    have hf1 : f (-1 : ℝ) = -1 / 5 := by
      field_simp [(show f (-1 : ℝ) ≠ 0 from by
        by_contra h0 
        rw [h0] at h3 
        norm_num at h3 
      )] at h3 ⊢ 
      linarith
    have hf33 : f (-3 : ℝ) = -5 := by
      rw [hf1] at h2 
      field_simp [(show f (-3 : ℝ) ≠ 0 from by
        by_contra h0 
        rw [h0] at h2 
        norm_num at h2 
      )] at h2 ⊢ 
      linarith
    rw [hf33] at h1 
    field_simp [(show f (-5 : ℝ) ≠ 0 from by
      by_contra h0 
      rw [h0] at h1 
      norm_num at h1 
    )] at h1 ⊢ 
    linarith
  
  rw [hf5] 
  exact_mod_cast hf55