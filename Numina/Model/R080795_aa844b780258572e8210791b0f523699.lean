import Mathlib

theorem algebra_275136 (x w : ℤ) (h₁ : 7 * x = 28) (h₂ : x + w = 9) : x * w = 20 := by 
  have hx : x = 4 := by 
    linarith
  have hw : w = 5 := by 
    rw [hx] at h₂
    linarith
  rw [hx, hw]
  norm_num