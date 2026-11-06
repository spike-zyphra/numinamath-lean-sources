import Mathlib

theorem inequalities_37477 (x y z k : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hk : 2 < k) (a b c : ℝ) (ha : a = x + k * y + k * z) (hb : b = k * x + y + k * z)
    (hc : c = k * x + k * y + z) :
    3 / (2 * k + 1) ≤ x / a + y / b + z / c := by
  rw [ha, hb, hc]
  have hk1 : 0 < k := by linarith
  have hk5 : 0 < (2 * k + 1 : ℝ) := by linarith
  have hk6 : 0 < x + k * y + k * z := by positivity
  have hk7 : 0 < k * x + y + k * z := by positivity
  have hk8 : 0 < k * x + k * y + z := by positivity
  have h2 : 3 / (2 * k + 1) - (x / (x + k * y + k * z) + y / (k * x + y + k * z) + z / (k * x + k * y + z)) ≤ 0 := by
    have h3 : 3 / (2 * k + 1) - (x / (x + k * y + k * z) + y / (k * x + y + k * z) + z / (k * x + k * y + z))
        = (3 * (x + k * y + k * z) * (k * x + y + k * z) * (k * x + k * y + z) - (x * (2 * k + 1) * (k * x + y + k * z) * (k * x + k * y + z) + y * (2 * k + 1) * (x + k * y + k * z) * (k * x + k * y + z) + z * (2 * k + 1) * (x + k * y + k * z) * (k * x + y + k * z))) / ((2 * k + 1) * (x + k * y + k * z) * (k * x + y + k * z) * (k * x + k * y + z)) := by
      field_simp
      ring
    rw [h3]
    have h4 : 3 * (x + k * y + k * z) * (k * x + y + k * z) * (k * x + k * y + z) - (x * (2 * k + 1) * (k * x + y + k * z) * (k * x + k * y + z) + y * (2 * k + 1) * (x + k * y + k * z) * (k * x + k * y + z) + z * (2 * k + 1) * (x + k * y + k * z) * (k * x + y + k * z)) ≤ 0 := by
      nlinarith [sq_nonneg (x * (k - 1) - y * (k - 1)), sq_nonneg (y * (k - 1) - z * (k - 1)), sq_nonneg (z * (k - 1) - x * (k - 1)), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (k - 2) + y * (k - 2) - z * (k - 2)), sq_nonneg (y * (k - 2) + z * (k - 2) - x * (k - 2)), sq_nonneg (z * (k - 2) + x * (k - 2) - y * (k - 2)), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
          mul_pos (show (0 : ℝ) < k - 2 by linarith) (show (0 : ℝ) < k by linarith), 
          mul_pos (show (0 : ℝ) < k - 2 by linarith) hx, 
          mul_pos (show (0 : ℝ) < k - 2 by linarith) hy, 
          mul_pos (show (0 : ℝ) < k - 2 by linarith) hz
        ]
    have h5 : (3 * (x + k * y + k * z) * (k * x + y + k * z) * (k * x + k * y + z) - (x * (2 * k + 1) * (k * x + y + k * z) * (k * x + k * y + z) + y * (2 * k + 1) * (x + k * y + k * z) * (k * x + k * y + z) + z * (2 * k + 1) * (x + k * y + k * z) * (k * x + y + k * z))) / ((2 * k + 1) * (x + k * y + k * z) * (k * x + y + k * z) * (k * x + k * y + z)) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg h4 (by positivity)
    exact h5
  linarith