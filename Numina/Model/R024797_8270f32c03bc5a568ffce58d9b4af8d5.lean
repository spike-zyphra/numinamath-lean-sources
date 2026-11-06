import Mathlib

theorem algebra_126458 (x y z a : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) (h : a / (x * y * z) = 1 / x + 1 / y + 1 / z - 2) :
    0 < a ∧ a ≤ 7 / 27 := by
  have h1 : 0 < x * y * z := by
    positivity
  have h2 : a = y * z + x * z + x * y - 2 * (x * y * z) := by
    have h3 : a / (x * y * z) = 1 / x + 1 / y + 1 / z - 2 := h
    have h4 : a = (a / (x * y * z)) * (x * y * z) := by
      field_simp
    rw [h4, h3]
    field_simp
    ring
  constructor
  · -- Show $a > 0$
    rw [h2]
    nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
              mul_pos (mul_pos hx hy) hz, 
              sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  · -- Show $a \le \frac{7}{27}$
    rw [h2]
    have h3 : z = 1 - x - y := by
      nlinarith
    rw [h3]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
              mul_pos hx hy, 
              mul_pos hx (show 0 < (1 - x - y) by nlinarith), 
              mul_pos hy (show 0 < (1 - x - y) by nlinarith), 
              sq_nonneg (x + y - (1 - x - y)), 
              mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith), 
              mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ (1 - x - y) by nlinarith), 
              mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ (1 - x - y) by nlinarith), 
              sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3), sq_nonneg ((1 - x - y) - 1 / 3)
            ]