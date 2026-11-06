import Mathlib

theorem inequalities_602954 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    33 ≤ 2 * (x ^ 3 + y ^ 3 + z ^ 3) / (x * y * z) + 9 * (x + y + z) ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2) := by

  have pos1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    all_goals linarith

  have pos2 : 0 < x ^ 2 + y ^ 2 + z ^ 2 := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]

  have h1 : 2 * (x ^ 3 + y ^ 3 + z ^ 3) / (x * y * z) + 9 * (x + y + z) ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2) - (33 : ℝ) ≥ 0 := by
    have h2 : 2 * (x ^ 3 + y ^ 3 + z ^ 3) / (x * y * z) + 9 * (x + y + z) ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2) - (33 : ℝ) =
        (2 * (x ^ 3 + y ^ 3 + z ^ 3) * (x ^ 2 + y ^ 2 + z ^ 2) + 9 * (x + y + z) ^ 2 * (x * y * z) - 33 * (x * y * z) * (x ^ 2 + y ^ 2 + z ^ 2)) / ((x * y * z) * (x ^ 2 + y ^ 2 + z ^ 2)) := by
      field_simp [pos1, pos2]
      <;> ring
    rw [h2] at *
    have h3 : (2 * (x ^ 3 + y ^ 3 + z ^ 3) * (x ^ 2 + y ^ 2 + z ^ 2) + 9 * (x + y + z) ^ 2 * (x * y * z) - 33 * (x * y * z) * (x ^ 2 + y ^ 2 + z ^ 2)) ≥ 0 := by
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
          sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)),
          sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
          sq_nonneg (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, mul_pos (mul_pos hx hy) hz]
    apply div_nonneg
    linarith
    positivity

  linarith