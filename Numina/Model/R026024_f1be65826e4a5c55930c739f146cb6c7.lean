import Mathlib

theorem algebra_158163 (w x y z : ℝ)
    (h1 : w + x + y + z = 5)
    (h2 : 2 * w + 4 * x + 8 * y + 16 * z = 7)
    (h3 : 3 * w + 9 * x + 27 * y + 81 * z = 11)
    (h4 : 4 * w + 16 * x + 64 * y + 256 * z = 1) :
    5 * w + 25 * x + 125 * y + 625 * z = -60 := by 
  have h5 : w + 3 * x + 7 * y + 15 * z = 2 := by 
    linarith [h1, h2]
  have h6 : w + 5 * x + 19 * y + 65 * z = 4 := by 
    linarith [h2, h3]
  have h7 : w + 7 * x + 37 * y + 175 * z = -10 := by 
    linarith [h3, h4]
  have h8 : 2 * x + 12 * y + 50 * z = 2 := by 
    linarith [h5, h6]
  have h9 : 2 * x + 18 * y + 110 * z = -14 := by 
    linarith [h6, h7]
  have h10 : 3 * y + 30 * z = -8 := by 
    linarith [h8, h9]
  have h11 : y + 10 * z = -8 / 3 := by 
    linarith
  have h12 : x = 17 + 35 * z := by
    have eq1 : 2 * x + 12 * y + 50 * z = 2 := by linarith [h8]
    have eq2 : y = -8 / 3 - 10 * z := by linarith [h11]
    rw [eq2] at eq1
    linarith
  have h13 : w = -91 / 3 - 50 * z := by
    have eq1 : w + 3 * x + 7 * y + 15 * z = 2 := by linarith [h5]
    have eq2 : x = 17 + 35 * z := by linarith [h12]
    have eq3 : y = -8 / 3 - 10 * z := by linarith [h11]
    rw [eq2, eq3] at eq1
    linarith
  have h14 : z = -7 / 8 := by 
    have eq1 : 4 * w + 16 * x + 64 * y + 256 * z = 1 := by linarith [h4]
    have eq2 : w = -91 / 3 - 50 * z := by linarith [h13]
    have eq3 : x = 17 + 35 * z := by linarith [h12]
    have eq4 : y = -8 / 3 - 10 * z := by linarith [h11]
    rw [eq2, eq3, eq4] at eq1
    linarith
  have hw : w = 161 / 12 := by
    linarith [h13, h14]
  have hx : x = -109 / 8 := by
    linarith [h12, h14]
  have hy : y = 73 / 12 := by
    linarith [h11, h14]
  linarith [hw, hx, hy, h14]