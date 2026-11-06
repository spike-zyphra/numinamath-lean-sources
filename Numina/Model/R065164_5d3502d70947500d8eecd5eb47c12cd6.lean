import Mathlib

theorem inequalities_11600 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 2) (h1 : x < 1) (h2 : y < 1) (h3 : z < 1) :
    1 < x * y + y * z + z * x ∧ x * y + y * z + z * x ≤ 4 / 3 := by
  constructor
  · -- Prove the lower bound 1 < xy + yz + zx
    nlinarith [h, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
              h1, h2, h3, mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2),
              mul_pos (sub_pos.mpr h1) (sub_pos.mpr h3), 
              mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3)]
  · -- Prove the upper bound xy + yz + zx ≤ 4/3
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
              h, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]