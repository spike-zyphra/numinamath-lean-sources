import Mathlib

theorem algebra_213201 {f : ℝ → ℝ} (h : ∀ x y, f (x + f y) = 2 * x + 2 * f (y + 1)) :
    ∀ x, f x = 2 * x + 4 := by

  have h1 : ∀ y, f (f y) = 2 * f (y + 1) := by
    intro y 
    specialize h 0 y 
    norm_num at h 
    all_goals simpa using h
  
  have h2 : ∀ x y, f x = 2 * x - 2 * f y + 2 * f (y + 1) := by 
    intro x y 
    have h3 := h (x - f y) y 
    rw [show (x - f y : ℝ) + f y = (x : ℝ) by ring] at h3 
    linarith
  
  -- Now we can derive expressions for f0 and f1
  -- First: From h3 : f 1 = 2*f0 - 2
  -- Second: From applying h2 with y=0 to get f x = 2x - 2f0 + 2f1. This leads to f1 = (f0/2) + f0
  -- The combination yields f0 = 4
  
  have h3 : f 1 = 2 * f 0 - 2 := by 
    specialize h2 1 0 
    norm_num at h2 
    linarith
  
  -- Get recurrence relation f(y+1) = f y + f0/2 
  have h4 : ∀ y, f (y + 1) = f y + f 0 / 2 := by 
    intro y 
    have h5 := h2 0 y 
    norm_num at h5 
    linarith
  
  have h50 : f 1 = (f 0 / 2) + f 0 := by 
    specialize h4 0 
    norm_num at h4 ⊢ 
    linarith
  
  -- Solve for f 0
  have h6 : f 0 = 4 := by 
    linarith [h3, h50] 

  -- Solve for f 1
  have h7 : f 1 = 6 := by 
    rw [h6] at h3 
    linarith
  
  -- Now since we can compute f 1, we can write the general form
  have h8 : ∀ x, f x = 2 * x + 4 := by 
    intro x
    have h10 : f x = 2 * x - 2 * f 0 + 2 * f (0 + 1) := by
      specialize h2 x 0 
      simpa using h2 
    -- Simplify f x expression, with f 0 = 4 and f 1 = 6 information
    have eq1 : f x = 2 * x - 2 * (4 : ℝ) + 2 * f 1 := by
      have eq2 : f (0 + (1 : ℝ)) = f 1 := by
        norm_num 
      rw [eq2] at h10 
      have h110 : f 0 = (4 : ℝ) := h6 
      rw [h110] at h10 
      all_goals linarith 
    rw [show f 1 = (6 : ℝ) by linarith [h7] ] at eq1
    all_goals linarith 
    all_goals linarith
  
  exact_mod_cast h8