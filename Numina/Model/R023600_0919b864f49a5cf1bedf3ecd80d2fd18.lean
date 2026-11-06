import Mathlib

theorem inequalities_599588 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxi : x < 1) (hyi : y < 1) (hzi : z < 1) :
    3 ≤ 1 / (1 - x + y) + 1 / (1 - y + z) + 1 / (1 - z + x) := by
  have hx1 : 0 < 1 - x + y := by nlinarith
  have hy1 : 0 < 1 - y + z := by nlinarith
  have hz1 : 0 < 1 - z + x := by nlinarith
  have h1 : 1 / (1 - x + y) + 1 / (1 - y + z) + 1 / (1 - z + x) - 3 ≥ 0 := by
    have h2 : 0 < (1 - x + y) * (1 - y + z) * (1 - z + x) := by positivity
    have h3 : (1 / (1 - x + y) + 1 / (1 - y + z) + 1 / (1 - z + x) - 3) = 
      ((1 - y + z) * (1 - z + x) + (1 - x + y) * (1 - z + x) + (1 - x + y) * (1 - y + z) - 3 * ((1 - x + y) * (1 - y + z) * (1 - z + x)) ) / ((1 - x + y) * (1 - y + z) * (1 - z + x)) := by 
        field_simp [show 0 < 1 - x + y by nlinarith, 
          show 0 < 1 - y + z by nlinarith, 
          show 0 < 1 - z + x by nlinarith]
        <;> ring
    rw [h3] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg ((1 - x + y) - (1 - y + z)), sq_nonneg ((1 - y + z) - (1 - z + x)), sq_nonneg ((1 - z + x) - (1 - x + y)),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
      mul_pos (sub_pos.mpr hxi) (sub_pos.mpr hyi), 
      mul_pos (sub_pos.mpr hxi) (sub_pos.mpr hzi), 
      mul_pos (sub_pos.mpr hyi) (sub_pos.mpr hzi)
    ]
    all_goals positivity
  linarith