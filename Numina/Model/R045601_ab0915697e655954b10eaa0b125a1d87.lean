import Mathlib

theorem inequalities_44948 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x < 1) (h2 : y < 1) (h3 : z < 1) :
    (1 - x) * y ≤ 1 / 4 ∨ (1 - y) * z ≤ 1 / 4 ∨ (1 - z) * x ≤ 1 / 4 := by 
  by_contra h
  push_neg at h
  nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (z - 1 / 2),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
          mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), 
          mul_pos (sub_pos.mpr h1) (sub_pos.mpr h3), 
          mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3)]