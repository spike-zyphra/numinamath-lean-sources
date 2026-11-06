import Mathlib

theorem inequalities_45838 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 = 3) :
    (x^2 + y * z) / (x^2 + y * z + 1) +
    (y^2 + z * x) / (y^2 + z * x + 1) +
    (z^2 + x * y) / (z^2 + x * y + 1) ≤ 2 := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : (x^2 + y * z) / (x^2 + y * z + 1) + (y^2 + z * x) / (y^2 + z * x + 1) + (z^2 + x * y) / (z^2 + x * y + 1) - 2 ≤ 0 := by
    have h4 : (x^2 + y * z) * (y^2 + z * x + 1) * (z^2 + x * y + 1) + (y^2 + z * x) * (x^2 + y * z + 1) * (z^2 + x * y + 1) + (z^2 + x * y) * (x^2 + y * z + 1) * (y^2 + z * x + 1) - 2 * (x^2 + y * z + 1) * (y^2 + z * x + 1) * (z^2 + x * y + 1) ≤ 0 := by
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
                sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
                sq_nonneg (x^2 + y^2 + z^2 - 3), sq_nonneg (x * y + y * z + z * x - 3),
                mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, mul_pos (show 0 < x * y from mul_pos hx hy) (show 0 < y * z from mul_pos hy hz)]
    have h3 : (x^2 + y * z) / (x^2 + y * z + 1) + (y^2 + z * x) / (y^2 + z * x + 1) + (z^2 + x * y) / (z^2 + x * y + 1) - 2 =
        ((x^2 + y * z) * (y^2 + z * x + 1) * (z^2 + x * y + 1) + (y^2 + z * x) * (x^2 + y * z + 1) * (z^2 + x * y + 1) + (z^2 + x * y) * (x^2 + y * z + 1) * (y^2 + z * x + 1) - 2 * (x^2 + y * z + 1) * (y^2 + z * x + 1) * (z^2 + x * y + 1)) / ((x^2 + y * z + 1) * (y^2 + z * x + 1) * (z^2 + x * y + 1)) := by
      field_simp
      ring
    rw [h3] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · positivity
  linarith