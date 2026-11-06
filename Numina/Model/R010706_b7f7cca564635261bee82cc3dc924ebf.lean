import Mathlib

theorem algebra_22130 {a b : ℝ} (h : ∀ t : ℝ, (3 * t ^ 2 + 5 * t + a) * (4 * t ^ 2 + b * t - 2) = 12 * t ^ 4 + 26 * t ^ 3 - 8 * t ^ 2 - 16 * t + 6) :
    a + b = -1 := by 
  have eq1 := h 0
  have ha : a = -3 := by 
    linarith 
  have eq2 := h 1 
  rw [ha] at eq2 
  have hb : b = 2 := by 
    nlinarith 
  linarith [ha, hb]