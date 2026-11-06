import Mathlib

theorem inequalities_130002 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxi : x < 1) (hyi : y < 1) (hzi : z < 1) :
    x * (1 - y) + y * (1 - z) + z * (1 - x) < 1 := by
  have hxy1 : x * y > 0 := mul_pos hx hy
  have hyz1 : y * z > 0 := mul_pos hy hz
  have hxz1 : x * z > 0 := mul_pos hx hz
  nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
          mul_pos (sub_pos.mpr hxi) (sub_pos.mpr hyi), 
          mul_pos (sub_pos.mpr hxi) (sub_pos.mpr hzi), 
          mul_pos (sub_pos.mpr hyi) (sub_pos.mpr hzi)
          ]