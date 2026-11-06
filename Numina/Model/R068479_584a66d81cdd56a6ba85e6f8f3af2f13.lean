import Mathlib

theorem inequalities_173661 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hx1 : x < 1) (hy1 : y < 1) (hz1 : z < 1) :
    x * (1 - y) + y * (1 - z) + z * (1 - x) < 1 := by 
  have h1 : x * (1 - y) + y * (1 - z) + z * (1 - x) = x + y + z - (x * y + y * z + z * x) := by
    ring
  rw [h1]
  nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
    mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hy1), mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hz1), mul_pos (sub_pos.mpr hy1) (sub_pos.mpr hz1),
    mul_pos (sub_pos.mpr hx1) (show 0 < 1 - z by linarith), mul_pos (sub_pos.mpr hy1) (show 0 < 1 - x by linarith), mul_pos (sub_pos.mpr hz1) (show 0 < 1 - y by linarith)]