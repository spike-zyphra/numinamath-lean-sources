import Mathlib

theorem inequalities_158945 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (z ^ 2 - x ^ 2) / (x + y) + (x ^ 2 - y ^ 2) / (y + z) + (y ^ 2 - z ^ 2) / (z + x) ≥ 0 := by

  have h1 : 0 < x + y := by linarith
  have h2 : 0 < y + z := by linarith
  have h3 : 0 < z + x := by linarith
  
  have h4 : (z ^ 2 - x ^ 2) / (x + y) + (x ^ 2 - y ^ 2) / (y + z) + (y ^ 2 - z ^ 2) / (z + x) =
      ((z ^ 2 - x ^ 2) * (y + z) * (z + x) + (x ^ 2 - y ^ 2) * (x + y) * (z + x) + (y ^ 2 - z ^ 2) * (x + y) * (y + z)) /
      ((x + y) * (y + z) * (z + x)) := by
    field_simp
    ring
  
  rw [h4]
  apply div_nonneg
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (y - z)), sq_nonneg (y * (z - x)), sq_nonneg (z * (x - y)), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz 
        ]
  all_goals positivity