import Mathlib

theorem inequalities_597855
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z) :
    3 / 4 ≤ x * y / ((y + z) * (z + x)) + y * z / ((z + x) * (x + y)) +
    z * x / ((x + y) * (y + z)) := by 
  have h1 : 0 < y + z := by linarith
  have h2 : 0 < z + x := by linarith
  have h3 : 0 < x + y := by linarith
  have h4 : 0 < (y + z) * (z + x) * (x + y) := by positivity
  have h5 : x * y / ((y + z) * (z + x)) + y * z / ((z + x) * (x + y)) + z * x / ((x + y) * (y + z)) - 3 / 4 ≥ 0 := by
    have hx1 : 0 < (y + z) * (z + x) * (x + y) := by positivity
    have h6 : (x * y / ((y + z) * (z + x)) + y * z / ((z + x) * (x + y)) + z * x / ((x + y) * (y + z)) - 3 / 4) =
          (x * y * (x + y) + y * z * (y + z) + z * x * (z + x) - 3 / 4 * ((y + z) * (z + x) * (x + y)) ) / ((y + z) * (z + x) * (x + y)) := by
      field_simp
      ring
    rw [h6]
    have h7 : ((y + z) * (z + x) * (x + y)) > 0 := by positivity
    apply div_nonneg 
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
      sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)),
      sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
    ]
    all_goals positivity 
    all_goals positivity
  linarith