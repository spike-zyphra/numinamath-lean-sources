import Mathlib

theorem inequalities_153014 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    0 ≤ (z ^ 2 - x ^ 2) / (x + y) + (x ^ 2 - y ^ 2) / (y + z) + (y ^ 2 - z ^ 2) / (z + x) := by
  have h1 : 0 < x + y := by linarith
  have h2 : 0 < y + z := by linarith
  have h3 : 0 < z + x := by linarith
  have h4 : 0 < (x + y) * (y + z) * (z + x) := by
    positivity
  have h5 : (z ^ 2 - x ^ 2) / (x + y) + (x ^ 2 - y ^ 2) / (y + z) + (y ^ 2 - z ^ 2) / (z + x) = 
          ((z ^ 2 - x ^ 2) * (y + z) * (z + x) + (x ^ 2 - y ^ 2) * (x + y) * (z + x) + (y ^ 2 - z ^ 2) * (x + y) * (y + z)) / ((x + y) * (y + z) * (z + x)) := by 
        field_simp
        ring
  rw [h5] at *
  apply div_nonneg
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + y - z), sq_nonneg (x + z - y), sq_nonneg (y + z - x),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
          mul_pos hx hz, mul_pos hy hz
          ]
  all_goals
    positivity