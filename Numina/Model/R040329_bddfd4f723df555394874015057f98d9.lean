import Mathlib

theorem inequalities_602846 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (k : ℝ) (hk : 1 < k) :
    x / (k * x + y + z) + y / (x + k * y + z) + z / (x + y + k * z) ≤ 3 / (k + 2) := by 
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz

  have h2 : 0 < k - 1 := by linarith
  have h3 : 0 < k * x + y + z := by
    nlinarith
  have h4 : 0 < x + k * y + z := by
    nlinarith
  have h5 : 0 < x + y + k * z := by
    nlinarith
  have h6 : 0 < (k * x + y + z) * (x + k * y + z) * (x + y + k * z) * (k + 2) := by
    positivity
  have h7 : x / (k * x + y + z) + y / (x + k * y + z) + z / (x + y + k * z) - 3 / (k + 2) ≤ 0 := by
    have h8 : x / (k * x + y + z) + y / (x + k * y + z) + z / (x + y + k * z) - 3 / (k + 2) = 
      ( 
        x * (x + k * y + z) * (x + y + k * z) * (k + 2) + 
        y * (k * x + y + z) * (x + y + k * z) * (k + 2) + 
        z * (k * x + y + z) * (x + k * y + z) * (k + 2) - 3 * (k * x + y + z) * (x + k * y + z) * (x + y + k * z) 
      ) / ( 
        (k * x + y + z) * (x + k * y + z) * (x + y + k * z) * (k + 2) 
      ) := by 
      field_simp 
      ring 
    rw [h8] 
    apply div_nonpos_of_nonpos_of_nonneg 
    nlinarith [sq_nonneg (x * (k - 1) - y * (k - 1) - z * (k - 1)), sq_nonneg (y * (k - 1) - x * (k - 1) - z * (k - 1)), sq_nonneg (z * (k - 1) - x * (k - 1) - y * (k - 1)), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg ((x * (k - 1)) - (y * (k - 1))), sq_nonneg ((y * (k - 1)) - (z * (k - 1))), sq_nonneg ((z * (k - 1)) - (x * (k - 1))), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
          mul_pos (sub_pos.mpr hk) (show 0 < x from hx), 
          mul_pos (sub_pos.mpr hk) (show 0 < y from hy), 
          mul_pos (sub_pos.mpr hk) (show 0 < z from hz)
        ]
    all_goals 
      positivity 
  linarith