import Mathlib

/- let x, y, z be strictly real numbers. Show that the following inequalities is true: x/(x + 2y + 3z) + y/(y+2z+3x) + z/(z+2x+3y) ≥ 1/2 -/
theorem inequalities_126655 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / (x + 2 * y + 3 * z) + y / (y + 2 * z + 3 * x) +
    z / (z + 2 * x + 3 * y) ≥ 1 / 2 := by
        have h1 : x / (x + 2 * y + 3 * z) + y / (y + 2 * z + 3 * x) + z / (z + 2 * x + 3 * y) ≥ 1 / 2 := by
            have h2 : x / (x + 2 * y + 3 * z) + y / (y + 2 * z + 3 * x) + z / (z + 2 * x + 3 * y) - 1 / 2 ≥ 0 := by
                have h3 : x / (x + 2 * y + 3 * z) + y / (y + 2 * z + 3 * x) + z / (z + 2 * x + 3 * y) - 1 / 2 =
                    (x * (y + 2 * z + 3 * x) * (z + 2 * x + 3 * y) + y * (z + 2 * x + 3 * y) * (x + 2 * y + 3 * z) + z * (x + 2 * y + 3 * z) * (y + 2 * z + 3 * x) - (1 / 2) * (x + 2 * y + 3 * z) * (y + 2 * z + 3 * x) * (z + 2 * x + 3 * y)) / ((x + 2 * y + 3 * z) * (y + 2 * z + 3 * x) * (z + 2 * x + 3 * y)) := by
                    field_simp
                    ring
                rw [h3]
                have h4 : (x + 2 * y + 3 * z) * (y + 2 * z + 3 * x) * (z + 2 * x + 3 * y) > 0 := by
                    apply mul_pos
                    apply mul_pos
                    nlinarith
                    nlinarith
                    nlinarith
                have h5 : x * (y + 2 * z + 3 * x) * (z + 2 * x + 3 * y) + y * (z + 2 * x + 3 * y) * (x + 2 * y + 3 * z) + z * (x + 2 * y + 3 * z) * (y + 2 * z + 3 * x) - (1 / 2) * (x + 2 * y + 3 * z) * (y + 2 * z + 3 * x) * (z + 2 * x + 3 * y) ≥ 0 := by
                    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
                apply div_nonneg
                linarith
                nlinarith
            linarith
        linarith [h1]
