import Mathlib

theorem algebra_15397 (x y : ℝ) (h1 : 2 * y = -x + 3) (h2 : -y = 5 * x + 1) :
    x = -5 / 9 ∧ y = 16 / 9 := by

  have h3 : y = -5 * x - 1 := by 
    linarith
  
  have hx : x = -5 / 9 := by 
    rw [h3] at h1
    linarith
  
  have hy : y = 16 / 9 := by
    rw [hx] at h3
    linarith
  
  exact ⟨hx, hy⟩