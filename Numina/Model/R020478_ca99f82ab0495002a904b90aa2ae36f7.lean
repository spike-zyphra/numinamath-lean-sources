import Mathlib

theorem inequalities_50991 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1 / x + 1 / y + 1 / z) : 3 ≤ x * y + y * z + z * x := by

  have h1 : 0 < x * y * z := by
    positivity

  have h2 : x * y * z * (x + y + z) = x * y + y * z + z * x := by
    field_simp at h ⊢
    nlinarith [h, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, mul_pos (show 0 < x * y by nlinarith) (show 0 < x * z by nlinarith), mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), mul_pos (show 0 < x * z by nlinarith) (show 0 < y * z by nlinarith)]

  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
    sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
    mul_pos (show 0 < x * y by nlinarith) (show 0 < x * z by nlinarith), 
    mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), 
    mul_pos (show 0 < x * z by nlinarith) (show 0 < y * z by nlinarith)]