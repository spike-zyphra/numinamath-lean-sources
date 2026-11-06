import Mathlib

theorem inequalities_8012 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    1 / (x ^ 2 + y * z) + 1 / (y ^ 2 + x * z) + 1 / (z ^ 2 + x * y) ≤
    1 / 2 * (1 / (x * y) + 1 / (x * z) + 1 / (y * z)) := by

  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    all_goals linarith

  have h2 : 1 / 2 * (1 / (x * y) + 1 / (x * z) + 1 / (y * z)) = (x + y + z) / (2 * x * y * z) := by
    field_simp
    ring

  rw [h2]

  have h3 : 1 / (x ^ 2 + y * z) + 1 / (y ^ 2 + x * z) + 1 / (z ^ 2 + x * y) ≤ (x + y + z) / (2 * x * y * z) := by

    have h4 : 0 < x ^ 2 + y * z := by
      positivity

    have h5 : 0 < y ^ 2 + x * z := by
      positivity

    have h6 : 0 < z ^ 2 + x * y := by
      positivity

    have h7 : 1 / (x ^ 2 + y * z) + 1 / (y ^ 2 + x * z) + 1 / (z ^ 2 + x * y) - (x + y + z) / (2 * x * y * z) ≤ 0 := by

      have h10 : 2 * x * y * z / (x ^ 2 + y * z) + 2 * x * y * z / (y ^ 2 + x * z) + 2 * x * y * z / (z ^ 2 + x * y) - (x + y + z) ≤ 0 := by

        have h15 : 2 * x * y * z / (x ^ 2 + y * z) ≤ (y + z) / 2 := by
          have h16 : 0 < x ^ 2 + y * z := by positivity
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith [ sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x * (y - z)), sq_nonneg (y * (y - z)), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
          ]

        have h16 : 2 * x * y * z / (y ^ 2 + x * z) ≤ (x + z) / 2 := by
          have h17 : 0 < y ^ 2 + x * z := by positivity
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith [ sq_nonneg (y - x), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (y * (x - z)), sq_nonneg (z * (z - x)), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
          ]

        have h17 : 2 * x * y * z / (z ^ 2 + x * y) ≤ (x + y) / 2 := by
          have h18 : 0 < z ^ 2 + x * y := by positivity
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith [ sq_nonneg (z - x), sq_nonneg (z - y), sq_nonneg (z * (x - y)), sq_nonneg (x * (x - y)), sq_nonneg (y * (x - y)), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
          ]

        linarith

      have h8 : 1 / (x ^ 2 + y * z) + 1 / (y ^ 2 + x * z) + 1 / (z ^ 2 + x * y) - (x + y + z) / (2 * x * y * z) =
          (2 * x * y * z / (x ^ 2 + y * z) + 2 * x * y * z / (y ^ 2 + x * z) + 2 * x * y * z / (z ^ 2 + x * y) - (x + y + z)) / (2 * x * y * z) := by
        field_simp
        <;> ring
      rw [h8]

      have h9 : 2 * x * y * z > 0 := by positivity
      apply div_nonpos_of_nonpos_of_nonneg h10 (by positivity)

    linarith

  linarith