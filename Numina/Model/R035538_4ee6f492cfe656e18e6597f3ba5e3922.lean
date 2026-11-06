import Mathlib

open Real

theorem algebra_3090 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 2020) :
    27 / 4080400 ≤ 1 / (x * y) + 1 / (x * z) + 1 / (y * z) := by
  have h1 : 1 / (x * y) + 1 / (x * z) + 1 / (y * z) = (x + y + z) / (x * y * z) := by
    field_simp
    <;> ring
  rw [h1, h]
  have h2 : 27 / 4080400 ≤ (2020 : ℝ) / (x * y * z) := by
    have h3 : x * y * z ≤ (2020 / 3) ^ 3 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
                  mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, sq_nonneg (x + y + z - 2020)]
    have h4 : 0 < x * y * z := by
      positivity
    have h5 : 27 * (x * y * z) ≤ (2020 : ℝ) ^ 3 := by
      nlinarith [h3]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h4, h5, (show (4080400 : ℝ) = (2020 : ℝ) ^ 2 by norm_num), h]
  simpa using h2