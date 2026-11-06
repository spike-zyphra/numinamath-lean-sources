import Mathlib

theorem algebra_13460 (a c d : ℝ) (h₀ : a > 0)
    (h₂ : c = 10) (h₃ : d = 24) (h₄ : a^2 = (c / 2)^2 + (d / 2)^2) :
    4 * a = 52 := by 
  rw [h₂, h₃] at h₄
  have ha : a = 13 := by
    nlinarith
  rw [ha]
  norm_num