import Mathlib

theorem algebra_237 {a b x : ℝ} (hx : x = (5^3 - 2^3)/7 * (5^3 + 2^3)/3) (h : x = (a^2 - b^2)) (h' : a - b = 19) : a^2 * b^2 = 84100 := by
  have hx2 : x = 741 := by 
    rw [hx]
    norm_num
  rw [hx2] at h 
  have eq1 : a^2 - b^2 = 741 := by linarith
  have eq2 : (a - b) * (a + b) = 741 := by
    have h1 : a^2 - b^2 = (a - b) * (a + b) := by ring
    linarith [h1, eq1]
  have eq3 : a + b = 39 := by
    rw [h'] at eq2
    linarith
  have ha : a = 29 := by
    linarith [h', eq3]
  have hb : b = 10 := by
    linarith [ha, h']
  rw [ha, hb]
  norm_num