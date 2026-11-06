import Mathlib

theorem inequalities_137395 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    3 / 4 ≤ x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) +
    z ^ 3 / ((1 + x) * (1 + y)) := by
  have hx1 : 0 < x := hx
  have hy1 : 0 < y := hy
  have hz1 : 0 < z := hz

  have h1 : 0 < (1 + y) * (1 + z) := by
    apply mul_pos
    linarith
    linarith
  have h2 : 0 < (1 + z) * (1 + x) := by
    apply mul_pos
    linarith
    linarith
  have h3 : 0 < (1 + x) * (1 + y) := by
    apply mul_pos
    linarith
    linarith
  have h4 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 ≥ 0 := by
    have h5 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 =
        (x^3 * (1 + x) + y^3 * (1 + y) + z^3 * (1 + z) - 3 / 4 * ( (1 + x) * (1 + y) * (1 + z) ) ) / ( (1 + y) * (1 + z) * (1 + x) ) := by 
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    have h6 : x^3 * (1 + x) + y^3 * (1 + y) + z^3 * (1 + z) - 3 / 4 * ( (1 + x) * (1 + y) * (1 + z) ) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        hxyz, mul_pos hx hy, mul_pos hy hz, mul_pos hx hz
      ]
    linarith
    positivity
  linarith