import Mathlib

theorem inequalities_122191 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (y ^ 2 + z ^ 2) / x + (z ^ 2 + x ^ 2) / y + (x ^ 2 + y ^ 2) / z ≥ 2 * (x + y + z) := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz

  have h2 : (y ^ 2 + z ^ 2) / x + (z ^ 2 + x ^ 2) / y + (x ^ 2 + y ^ 2) / z - 2 * (x + y + z) ≥ 0 := by
    have h3 : (y ^ 2 + z ^ 2) / x + (z ^ 2 + x ^ 2) / y + (x ^ 2 + y ^ 2) / z - 2 * (x + y + z) =
        ((y ^ 2 + z ^ 2) * (y * z) + (z ^ 2 + x ^ 2) * (x * z) + (x ^ 2 + y ^ 2) * (x * y) - 2 * (x + y + z) * (x * y * z)) / (x * y * z) := by
      field_simp
      ring
      <;> field_simp
      <;> ring

    rw [h3]

    have h4 : (y ^ 2 + z ^ 2) * (y * z) + (z ^ 2 + x ^ 2) * (x * z) + (x ^ 2 + y ^ 2) * (x * y) - 2 * (x + y + z) * (x * y * z) ≥ 0 := by
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
        sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)),
        sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
      ]

    apply div_nonneg
    linarith
    linarith
  linarith