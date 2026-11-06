import Mathlib

theorem algebra_189049 (x y z t : ℤ) (h : x * y - x * z + y * t = 182)
    (h1 : x = 12) (h2 : y = 37) (h3 : z = 65) : t = 14 := by 
  rw [h1, h2, h3] at h
  linarith