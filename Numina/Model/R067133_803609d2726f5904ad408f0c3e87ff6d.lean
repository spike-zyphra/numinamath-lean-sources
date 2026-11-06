import Mathlib

theorem algebra_244617 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (hf : ∀ x, f (x + 2) = -f x) :
    f 6 = 0 := by
  have h1 : f 6 = -f 4 := by 
    specialize hf 4
    norm_num at hf ⊢
    linarith 
  have h2 : f 4 = -f 2 := by 
    specialize hf 2
    norm_num at hf ⊢
    linarith 
  have h3 : f 2 = -f 0 := by 
    specialize hf 0
    norm_num at hf ⊢
    linarith 
  have h4 : f 0 = 0 := by 
    specialize hodd 0 
    norm_num at hodd 
    linarith 
  rw [h4] at h3 
  rw [h3] at h2 
  rw [h2] at h1 
  norm_num at h1 
  linarith