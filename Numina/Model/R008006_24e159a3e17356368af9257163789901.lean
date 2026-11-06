import Mathlib

theorem algebra_10559 (x y z : ℝ) (h : x * y * z = 108) :
    (x / 3) * (y / 3) * (z / 3) = 4 := by 
  have h1 : (x / 3) * (y / 3) * (z / 3) = (x * y * z) / 27 := by 
    ring 
  rw [h1, h]
  norm_num