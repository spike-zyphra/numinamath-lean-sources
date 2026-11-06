import Mathlib

theorem inequalities_114479 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    6 ≤ x / y + y / z + z / x + x / z + z / y + y / x := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz

  have h2 : x / y + y / z + z / x + x / z + z / y + y / x - 6 ≥ 0 := by
    have pos1 : 0 < x := hx
    have pos2 : 0 < y := hy
    have pos3 : 0 < z := hz
    have pos4 : 0 < x * y := by
      apply mul_pos
      exact hx
      exact hy
    have pos5 : 0 < x * z := by
      apply mul_pos
      exact hx
      exact hz
    have pos6 : 0 < y * z := by
      apply mul_pos
      exact hy
      exact hz

    have h3 : x / y + y / z + z / x + x / z + z / y + y / x - 6 = 
        (x ^ 2 * z + x * y ^ 2 + y * z ^ 2 + x ^ 2 * y + x * z ^ 2 + y ^ 2 * z - 6 * x * y * z) / (x * y * z) := by
      field_simp [pos1, pos2, pos3]
      ring

    rw [h3]

    apply div_nonneg

    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
          ]

    positivity
  
  linarith