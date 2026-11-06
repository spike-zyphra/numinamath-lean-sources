import Mathlib

theorem algebra_197015 (v m : ℝ) (h₀ : v = 63) (h₁ : m = v + 4) (h₂ : v * m + v * 63 = 2016 * 150) :
    v * 63 = 170100 := by 
  rw [h₀] at h₁ -- m = 63 + 4
  have hm : m = 67 := by
    linarith [h₁]
  rw [show m = 67 by linarith [hm], show v = 63 by linarith [h₀]] at h₂
  nlinarith