import Mathlib

theorem algebra_1051 {a b c d : ℚ} (h1 : a + 2 * b = 10) (h2 : c + 2 * d = 10) (h3 : a * c + 4 * b * d = 30) : a * d + b * c = 35 := by 
  have ha : a = 10 - 2 * b := by linarith
  have hc : c = 10 - 2 * d := by linarith
  rw [ha, hc] at h3
  have had : a * d + b * c = 10 * (b + d) - 4 * (b * d) := by
    rw [show a = 10 - 2 * b by linarith [h1], show c = 10 - 2 * d by linarith [h2]]
    ring
  have eq1 : 8 * (b * d) - 20 * (b + d) + 70 = 0 := by
    nlinarith 
  have eq2 : 8 * (b * d) = 20 * (b + d) - 70 := by
    linarith 
  have eq3 : a * d + b * c = 35 := by
    rw [had]
    have h4 : 4 * (b * d) = (20 * (b + d) - 70)/2 := by 
      have h5 : 8 * (b * d) = 20 * (b + d) - 70 := by linarith [eq1]
      linarith 
    linarith [h4]
  linarith [eq3]