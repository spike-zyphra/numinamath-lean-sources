import Mathlib

theorem algebra_133871 {f : ℝ → ℝ} (h : ∀ x, x ≥ 2 → f x = x) (h' : ∀ x, 0 ≤ x ∧ x < 2 → f x = f (4 - x)) (h'' : ∀ x, x < 0 → f x = f (x + 2)) : f (-5) = 3 := by 

  -- Since -5 < 0, apply the third case: f(-5) = f(-5 + 2) = f(-3)
  have h1 : f (-5) = f (-3) := by 
    specialize h'' (-5) (by norm_num)
    norm_num at h''
    linarith
  
  -- Since -3 < 0, apply the third case: f(-3) = f(-3 + 2) = f(-1)
  have h2 : f (-3) = f (-1) := by 
    specialize h'' (-3) (by norm_num)
    norm_num at h''
    linarith
  
  -- Since -1 < 0, apply the third case: f(-1) = f(-1 + 2) = f(1)
  have h3 : f (-1) = f (1) := by 
    specialize h'' (-1) (by norm_num)
    norm_num at h''
    linarith
  
  -- Since 0 ≤ 1 < 2, apply the second case: f(1) = f(4 - 1) = f(3)
  have h4 : f (1) = f (3) := by 
    specialize h' 1 (by norm_num)
    norm_num at h'
    linarith
  
  -- Since 3 ≥ 2, apply the first case: f(3) = 3
  have h5 : f (3) = 3 := by 
    specialize h 3 (by norm_num)
    linarith
  
  -- Combine all the steps to conclude f(-5) = 3
  linarith [h1, h2, h3, h4, h5]