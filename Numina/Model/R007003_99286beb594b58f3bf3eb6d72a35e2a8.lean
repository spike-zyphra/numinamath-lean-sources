import Mathlib

theorem algebra_21989 (a d : ℝ) (h₁ : a + 14 = a + 2 * d) (h₂ : (a / 2 + a) + (a / 2 + a + d) + (a / 2 + a + d * 2) = 120) :
    a = 22 := by 
  have hd : d = 7 := by
    linarith
  rw [hd] at h₂
  linarith