import Mathlib

theorem inequalities_224777 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    3 / 4 ≤ x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) +
    z ^ 3 / ((1 + x) * (1 + y)) := by

  have h3 : 0 < (1 + y) * (1 + z) := by
    positivity

  have h4 : 0 < (1 + z) * (1 + x) := by
    positivity

  have h5 : 0 < (1 + x) * (1 + y) := by
    positivity

  have h6 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 ≥ 0 := by
    have h7 : 0 < (1 + y) * (1 + z) * (1 + x) := by
      positivity
    have h8 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 =
        (x ^ 3 * (1 + x) + y ^ 3 * (1 + y) + z ^ 3 * (1 + z) - 3 / 4 * ((1 + y) * (1 + z) * (1 + x)) ) / ((1 + y) * (1 + z) * (1 + x)) := by
      field_simp
      ring
    have h9 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 ≥ 0 := by
      have h10 : (x ^ 3 * (1 + x) + y ^ 3 * (1 + y) + z ^ 3 * (1 + z) - 3 / 4 * ((1 + y) * (1 + z) * (1 + x)) ) ≥ 0 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
            sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
            hxyz, mul_pos hx hy, mul_pos hy hz, mul_pos hx hz
          ]
      have h5 : (1 + y) * (1 + z) * (1 + x) > 0 := by
        positivity
      have h11 : (x ^ 3 * (1 + x) + y ^ 3 * (1 + y) + z ^ 3 * (1 + z) - 3 / 4 * ((1 + y) * (1 + z) * (1 + x)) ) / ((1 + y) * (1 + z) * (1 + x)) ≥ 0 := by
        apply div_nonneg
        linarith
        all_goals
          positivity
      linarith
    linarith [h8, h9]

  linarith [h6]