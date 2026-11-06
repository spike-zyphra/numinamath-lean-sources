import Mathlib

theorem algebra_96124 (a c x: ℝ) (h : a = 2 * c) (h₀ : 5 * a + 4 * c = 24.50) (h₁ : 8 * a + 6 * c = x) : x = 38.50 := by
  have h2 : c = 1.75 := by 
    rw [show a = 2 * c by linarith [h]] at h₀
    norm_num at h₀
    linarith
  have ha : a = 3.50 := by
    rw [h2] at h
    norm_num at h
    linarith
  have h3 : 8 * a + 6 * c = 38.50 := by
    rw [show a = 3.50 by linarith [ha], show c = 1.75 by linarith [h2]]
    norm_num
  linarith [h₁, h3]