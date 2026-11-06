import Mathlib

theorem algebra_94600 (x y : ℝ) (h : (3 * x - 4) / (y + 15) = (3 * 2 - 4) / (3 + 15)) (hy : y = 12) :
    x = 7 / 3 := by 
  rw [hy] at h
  have eq1 : 3 * x - 4 = 3 := by 
    norm_num at h 
    field_simp [(show ( (12 + 15 : ℝ ) ) ≠ 0 by norm_num)] at h 
    linarith 
  linarith [eq1]