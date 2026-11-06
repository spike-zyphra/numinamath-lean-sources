import Mathlib

theorem inequalities_120764 (x y : ℝ) (hx : abs x < 1) (hy : abs y < 1) :
    abs ((x - y) / (1 - x * y)) < 1 := by
  have h1 : -1 < x := by
    linarith [abs_lt.mp hx]
  have h2 : x < 1 := by
    linarith [abs_lt.mp hx]
  have h3 : -1 < y := by
    linarith [abs_lt.mp hy]
  have h4 : y < 1 := by
    linarith [abs_lt.mp hy]
  have h5 : 0 < 1 - x * y := by
    nlinarith [mul_pos (show 0 < 1 - x by linarith) (show 0 < 1 - y by linarith), 
      mul_pos (show 0 < 1 + x by linarith) (show 0 < 1 + y by linarith), 
      mul_pos (show 0 < 1 - x by linarith) (show 0 < 1 + y by linarith), 
      mul_pos (show 0 < 1 + x by linarith) (show 0 < 1 - y by linarith)]
  have h6 : - (1 - x * y) < x - y := by
    nlinarith [mul_pos (show 0 < 1 - x by linarith) (show 0 < 1 - y by linarith), 
      mul_pos (show 0 < 1 + x by linarith) (show 0 < 1 + y by linarith)]
  have h7 : x - y < 1 - x * y := by
    nlinarith [mul_pos (show 0 < 1 - x by linarith) (show 0 < 1 - y by linarith), 
      mul_pos (show 0 < 1 + x by linarith) (show 0 < 1 + y by linarith)]
  have h8 : -1 < (x - y) / (1 - x * y) := by
    apply (lt_div_iff₀ h5).mpr
    linarith 
  have h9 : (x - y) / (1 - x * y) < 1 := by
    apply (div_lt_iff₀ h5).mpr
    linarith 
  rw [abs_lt]
  constructor <;> linarith [h8, h9]