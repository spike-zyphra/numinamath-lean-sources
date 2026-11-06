import Mathlib

theorem inequalities_54905 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x * y + y * z + z * x) * (1 / (x ^ 2 + y ^ 2) + 1 / (y ^ 2 + z ^ 2) + 1 / (z ^ 2 + x ^ 2)) > 5 / 2 := by
  have h1 : 0 < x * y := mul_pos hx hy
  have h2 : 0 < x * z := mul_pos hx hz
  have h3 : 0 < y * z := mul_pos hy hz

  have h4 : 0 < x ^ 2 + y ^ 2 := by nlinarith [hx, hy, h1]
  have h5 : 0 < y ^ 2 + z ^ 2 := by nlinarith [hy, hz, h2]
  have h6 : 0 < z ^ 2 + x ^ 2 := by nlinarith [hz, hx, h3]

  have h7 : (x * y + y * z + z * x) * (1 / (x ^ 2 + y ^ 2) + 1 / (y ^ 2 + z ^ 2) + 1 / (z ^ 2 + x ^ 2)) - 5 / 2 > 0 := by
    have pos1 : 0 < (x ^ 2 + y ^ 2) * (y ^ 2 + z ^ 2) * (z ^ 2 + x ^ 2) := by positivity
    have h9 : (x * y + y * z + z * x) * (1 / (x ^ 2 + y ^ 2) + 1 / (y ^ 2 + z ^ 2) + 1 / (z ^ 2 + x ^ 2)) - 5 / 2 =
        ((x * y + y * z + z * x) * ((y ^ 2 + z ^ 2) * (z ^ 2 + x ^ 2) + (x ^ 2 + y ^ 2) * (z ^ 2 + x ^ 2) + (x ^ 2 + y ^ 2) * (y ^ 2 + z ^ 2)) - (5 / 2) * (x ^ 2 + y ^ 2) * (y ^ 2 + z ^ 2) * (z ^ 2 + x ^ 2)) / ((x ^ 2 + y ^ 2) * (y ^ 2 + z ^ 2) * (z ^ 2 + x ^ 2)) := by 
      field_simp
      ring
    rw [h9]
    apply div_pos 
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
          sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)),
          sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3
        ]
    all_goals positivity
  linarith