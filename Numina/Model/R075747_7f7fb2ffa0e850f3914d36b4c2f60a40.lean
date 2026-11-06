import Mathlib

theorem inequalities_7316 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    1 / (x + y + 1) + 1 / (y + z + 1) + 1 / (z + x + 1) ≤ 1 := by
  have h1 : 0 < x * y := by
    nlinarith
  have h2 : 0 < y * z := by
    nlinarith
  have h3 : 0 < z * x := by
    nlinarith
  have h4 : (x + y + 1) * (y + z + 1) * (z + x + 1) > 0 := by
    positivity
  have h5 : (x + y + 1) > 0 := by
    nlinarith
  have h6 : (y + z + 1) > 0 := by
    nlinarith
  have h7 : (z + x + 1) > 0 := by
    nlinarith
  have h8 : 1 / (x + y + 1) + 1 / (y + z + 1) + 1 / (z + x + 1) - 1 ≤ 0 := by
    have h9 : (1 / (x + y + 1) + 1 / (y + z + 1) + 1 / (z + x + 1) - 1) =
        ((y + z + 1) * (z + x + 1) + (x + y + 1) * (z + x + 1) + (x + y + 1) * (y + z + 1) - (x + y + 1) * (y + z + 1) * (z + x + 1)) / ((x + y + 1) * (y + z + 1) * (z + x + 1)) := by
      field_simp [(show x + y + 1 ≠ 0 by positivity), (show y + z + 1 ≠ 0 by positivity), (show z + x + 1 ≠ 0 by positivity)]
      ring
    rw [h9]
    have h10 : ((y + z + 1) * (z + x + 1) + (x + y + 1) * (z + x + 1) + (x + y + 1) * (y + z + 1) - (x + y + 1) * (y + z + 1) * (z + x + 1)) ≤ 0 := by
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          hxyz, mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]
    have h11 : (x + y + 1) * (y + z + 1) * (z + x + 1) > 0 := by positivity
    apply div_nonpos_of_nonpos_of_nonneg
    linarith
    all_goals linarith
  linarith