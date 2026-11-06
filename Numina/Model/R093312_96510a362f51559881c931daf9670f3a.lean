import Mathlib

theorem algebra_1042 {a b c : ℝ} (h1 : a + b = 3) (h2 : a * c + b = 18) (h3 : b * c + a = 6) :
    c = 7 := by 
  have hb : b = 3 - a := by linarith 
  rw [hb] at h2 h3 
  have eq1 : a * (c - 1) = 15 := by 
    linarith 
  have eq2 : 3 * c - (a * (c - 1)) = 6 := by
    nlinarith 
  rw [eq1] at eq2 
  linarith