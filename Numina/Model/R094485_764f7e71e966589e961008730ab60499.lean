import Mathlib

theorem algebra_163244 {f : ℝ → ℝ} (h : ∀ x, x + f x = f (f x)) :
    f (f x) = 0 ↔ x = 0 := by
  constructor
  · -- Assume f(f(x)) = 0, prove x = 0
    intro h1
    have h2 : x + f x = 0 := by 
      specialize h x 
      rw [h1] at h 
      linarith
    have hfx : f x = -x := by 
      linarith 
    have h3 : f (-x) = 0 := by 
      rw [show f x = -x by linarith [hfx]] at h1
      linarith 
    have h4 : -x + f (-x) = f (f (-x)) := by 
      specialize h (-x) 
      simpa using h 
    rw [h3] at h4
    have h5 : f 0 = -x := by 
      linarith 
    have h6 : f 0 = f (f 0) := by 
      specialize h 0 
      simpa using h 
    have h7 : f (f 0) = 0 := by 
      rw [show f 0 = -x by linarith [h5]] 
      linarith [h3] 
    have h9 : f 0 = 0 := by 
      linarith [h6, h7] 
    linarith [h5, h9] 
  · -- Assume x = 0, prove f(f(x)) = 0
    intro h2
    rw [h2]
    have h3 : f 0 = f (f 0) := by 
      specialize h 0 
      simpa using h 
    have h4 : f 0 + f (f 0) = f (f (f 0)) := by 
      specialize h (f 0)
      simpa using h 
    have h5 : f (f (f 0)) = f (f 0) := by 
      rw [show f (f 0) = f 0 by linarith [h3]]
      all_goals linarith
    have h6 : f 0 + f (f 0) = f 0 := by 
      nlinarith [h4, h5, h3] 
    have h7 : f 0 = 0 := by 
      nlinarith [h6, h3] 
    rw [show f 0 = 0 by linarith [h7]]
    all_goals linarith [h7]