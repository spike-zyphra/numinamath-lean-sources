import Mathlib

open Real

theorem inequalities_234930 (x y z t : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1)
    (hz : 0 < z ∧ z < 1) (ht : 0 < t ∧ t < 1) :
    sqrt (x ^ 2 + (1 - t) ^ 2) + sqrt (y ^ 2 + (1 - x) ^ 2) +
    sqrt (z ^ 2 + (1 - y) ^ 2) + sqrt (t ^ 2 + (1 - z) ^ 2) < 4 := by

  have h1 : sqrt (x ^ 2 + (1 - t) ^ 2) < x + (1 - t) := by 
    have h2 : x ^ 2 + (1 - t) ^ 2 < (x + (1 - t)) ^ 2 := by 
      nlinarith [mul_pos hx.1 (show 0 < 1 - t by linarith [ht.2]), mul_pos (show 0 < 1 - t by linarith [ht.2]) hx.1]
    have h3 : sqrt (x ^ 2 + (1 - t) ^ 2) < sqrt ((x + (1 - t)) ^ 2) := Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
    rw [Real.sqrt_sq (by linarith)] at h3
    linarith

  have h2 : sqrt (y ^ 2 + (1 - x) ^ 2) < y + (1 - x) := by 
    have h2 : y ^ 2 + (1 - x) ^ 2 < (y + (1 - x)) ^ 2 := by 
      nlinarith [mul_pos hy.1 (show 0 < 1 - x by linarith [hx.2]), mul_pos (show 0 < 1 - x by linarith [hx.2]) hy.1]
    have h3 : sqrt (y ^ 2 + (1 - x) ^ 2) < sqrt ((y + (1 - x)) ^ 2) := Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
    rw [Real.sqrt_sq (by linarith)] at h3
    linarith

  have h3 : sqrt (z ^ 2 + (1 - y) ^ 2) < z + (1 - y) := by 
    have h2 : z ^ 2 + (1 - y) ^ 2 < (z + (1 - y)) ^ 2 := by 
      nlinarith [mul_pos hz.1 (show 0 < 1 - y by linarith [hy.2]), mul_pos (show 0 < 1 - y by linarith [hy.2]) hz.1]
    have h3 : sqrt (z ^ 2 + (1 - y) ^ 2) < sqrt ((z + (1 - y)) ^ 2) := Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
    rw [Real.sqrt_sq (by linarith)] at h3
    linarith

  have h4 : sqrt (t ^ 2 + (1 - z) ^ 2) < t + (1 - z) := by 
    have h2 : t ^ 2 + (1 - z) ^ 2 < (t + (1 - z)) ^ 2 := by 
      nlinarith [mul_pos ht.1 (show 0 < 1 - z by linarith [hz.2]), mul_pos (show 0 < 1 - z by linarith [hz.2]) ht.1]
    have h3 : sqrt (t ^ 2 + (1 - z) ^ 2) < sqrt ((t + (1 - z)) ^ 2) := Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
    rw [Real.sqrt_sq (by linarith)] at h3
    linarith

  nlinarith