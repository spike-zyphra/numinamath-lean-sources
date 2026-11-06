import Mathlib

open Real

theorem inequalities_3815 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (3 / 2)^2 ≥ (x / (x + y) + y / (y + z) + z / (z + x)) *
      (z / (y + z) + y / (x + y) + x / (z + x)) := by
  have h1 : 0 < (x + y) * (y + z) * (z + x) := by
    positivity
  have h2 : (x / (x + y) + y / (y + z) + z / (z + x)) + (z / (y + z) + y / (x + y) + x / (z + x)) = 3 := by
    field_simp [(show (x + y : ℝ) ≠ 0 by positivity), (show (y + z : ℝ) ≠ 0 by positivity), (show (z + x : ℝ) ≠ 0 by positivity)]
    ring
  have h3 : (3 / 2)^2 ≥ (x / (x + y) + y / (y + z) + z / (z + x)) * (z / (y + z) + y / (x + y) + x / (z + x)) := by
    nlinarith [sq_nonneg (x / (x + y) + y / (y + z) + z / (z + x) - 3 / 2), sq_nonneg (z / (y + z) + y / (x + y) + x / (z + x) - 3 / 2), 
      h2, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
      ]
  exact h3