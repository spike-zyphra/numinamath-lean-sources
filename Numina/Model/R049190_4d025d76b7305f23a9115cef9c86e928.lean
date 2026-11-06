import Mathlib

theorem other_62721 (u : ℤ → ℝ) (h : ∀ n, u (n + 2) = 2 * u (n + 1) + u n)
    (hu3 : u 3 = 9) (hu6 : u 6 = 128) : u 5 = 53 := by

  have eq1 : u 4 = 2 * u 3 + u 2 := by 
    specialize h 2
    norm_num at h ⊢
    linarith

  rw [hu3] at eq1
  
  have eq2 : u 5 = 2 * u 4 + u 3 := by 
    specialize h 3
    norm_num at h ⊢
    linarith
  
  rw [eq1, hu3] at eq2
  
  have eq3 : u 6 = 2 * u 5 + u 4 := by 
    specialize h 4
    norm_num at h ⊢
    linarith
  
  rw [eq2, eq1] at eq3
  
  rw [hu6] at eq3
  
  have hu2 : u 2 = 4 := by 
    linarith
  
  rw [hu2] at eq2
  
  linarith