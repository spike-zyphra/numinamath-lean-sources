import Mathlib

theorem algebra_3416 (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
(h₁ : d = a + b + c) (h₂ : c = d + 1.36) (h₃ : a + b = 43.12) :
a + b + c + d = 56.32 := by 
  have h5 : a + b = 43.12 := by linarith
  have h6 : c = d + 1.36 := by linarith
  rw [show a + b = 43.12 by linarith] at h₁
  rw [h6] at h₁
  norm_num at h₁
  linarith