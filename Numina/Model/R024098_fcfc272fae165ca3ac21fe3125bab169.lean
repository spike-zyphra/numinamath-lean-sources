import Mathlib

theorem algebra_318642 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z * (x + y + z) = 1) :
    (x + y) * (y + z) ≥ 2 := by

  have h2 : (x + y) * (y + z) = y * (x + y + z) + x * z := by
    ring

  rw [h2]

  have h3 : 0 < x * z := by
    nlinarith
  
  have h4 : 0 < y * (x + y + z) := by
    positivity
  
  have h5 : y * (x + y + z) * (x * z) = 1 := by
    nlinarith
  
  nlinarith [sq_nonneg (y * (x + y + z) - 1), sq_nonneg (x * z - 1), 
    sq_nonneg (y * (x + y + z) - x * z), 
    mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
    mul_pos (show 0 < x * y from by nlinarith) (show 0 < y * z from by nlinarith)
  ]