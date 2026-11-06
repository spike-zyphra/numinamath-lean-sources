import Mathlib
open Function

theorem algebra_3998 {f : ℝ → ℝ} (hinjective : Injective f)
(h : ∀ x y, f (x + f y) = 2012 + f (x + y)) :
f 2013 = 4025 := by

  have h1 : ∀ y, f (f y) = 2012 + f y := by
    intro y 
    specialize h 0 y
    norm_num at h 
    simpa using h
  
  have h2 : ∀ y, f (2 * f y - y) = 4024 + f y := by 
    intro y 
    have eq1 := h (f y - y) y 
    have eq1' : f ((f y - y) + f y) = 2012 + f ((f y - y) + y) := by 
      simpa using eq1 
    have eq2 : (f y - y) + f y = 2 * f y - y := by ring
    have eq3 : (f y - y) + y = f y := by ring 
    rw [eq2] at eq1' 
    have eq4 : f ((f y - y) + y) = f (f y) := by 
      rw [eq3] 
    rw [eq4] at eq1' 
    have eq5 : f (f y) = 2012 + f y := h1 y 
    rw [eq5] at eq1' 
    linarith
  
  have h3 : ∀ y, f (f (f y)) = 4024 + f y := by 
    intro y 
    have eq1 : f (f y) = 2012 + f y := h1 y 
    have eq2 : f (f (f y)) = 2012 + f (f y) := by 
      apply h1 
    rw [eq2, eq1]
    all_goals linarith
  
  have h4 : ∀ y, 2 * f y - y = f (f y) := by 
    intro y 
    have eq1 : f (2 * f y - y) = 4024 + f y := h2 y 
    have eq2 : f (f (f y)) = 4024 + f y := h3 y 
    have h5 : f (2 * f y - y) = f (f (f y)) := by 
      linarith [eq1, eq2] 
    have h6 : (2 * f y - y) = f (f y) := by 
      apply hinjective 
      exact h5 
    linarith
  
  have h5' : ∀ y, f y = y + 2012 := by 
    intro y 
    have eq1 : 2 * f y - y = f (f y) := h4 y 
    have eq2 : f (f y) = 2012 + f y := h1 y 
    rw [eq2] at eq1 
    linarith

  have eq3 : f 2013 = 2013 + 2012 := by 
    apply h5' 

  linarith