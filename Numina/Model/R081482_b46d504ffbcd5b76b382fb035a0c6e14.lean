import Mathlib

theorem algebra_15007 {k : ℤ} (a b : ℤ) (h : ∀ k : ℤ, 4 * k + 8 = 4 * (a * k + b)) :
    (a : ℚ) / b = 1 / 2 := by 
  have eq1 := h 0
  have eq2 := h 1
  have hb : b = 2 := by
    linarith 
  have ha : a = 1 := by 
    rw [hb] at eq2 
    linarith 
  rw [ha, hb]
  all_goals norm_num