import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_222935 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (hsum : x + y + z = 1) :
  1 / x + 4 / y + 9 / z ≥ 36 := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz
  have h2 : 1 / x + 4 / y + 9 / z - 36 ≥ 0 := by
    have h3 : 1 / x + 4 / y + 9 / z - 36 = (y * z + 4 * x * z + 9 * x * y - 36 * (x * y * z)) / (x * y * z) := by
      field_simp [hx.ne.symm, hy.ne.symm, hz.ne.symm]
      ring
    rw [h3]
    have h4 : y * z + 4 * x * z + 9 * x * y - 36 * (x * y * z) ≥ 0 := by
      nlinarith [sq_nonneg (x - 1 / 6), sq_nonneg (y - 1 / 3), sq_nonneg (z - 1 / 2),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, hsum
        ]
    have h5 : x * y * z > 0 := h1
    have h6 : y * z + 4 * x * z + 9 * x * y - 36 * (x * y * z) ≥ 0 := h4
    apply div_nonneg
    linarith
    all_goals nlinarith
  linarith