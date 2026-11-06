import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_144121 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (h : x + y + z = 1) :
  1 / x + 4 / y + 9 / z ≥ 36 := by 
  have pos1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h1 : 1 / x + 4 / y + 9 / z - 36 ≥ 0 := by
    have h2 : 1 / x + 4 / y + 9 / z - 36 = (y * z + 4 * x * z + 9 * x * y - 36 * x * y * z) / (x * y * z) := by
      field_simp [hx.ne.symm, hy.ne.symm, hz.ne.symm]
      ring
    rw [h2]
    apply div_nonneg
    nlinarith [sq_nonneg (x - 1 / 6), sq_nonneg (y - 1 / 3), sq_nonneg (z - 1 / 2), 
      sq_nonneg (x - y / 2), sq_nonneg (y - 2 * x), sq_nonneg (z - 3 * x),
      sq_nonneg (x - 1 / 6), sq_nonneg (y - 1 / 3), sq_nonneg (z - 1 / 2), 
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, h]
    positivity
  linarith