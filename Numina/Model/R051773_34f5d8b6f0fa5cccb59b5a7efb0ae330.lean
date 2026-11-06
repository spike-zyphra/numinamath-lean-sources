import Mathlib

theorem inequalities_603306
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    3 / 4 ≤ x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) +
    z ^ 3 / ((1 + x) * (1 + y)) := by
  have hxy : 0 < x * y := by
    nlinarith
  have hxz : 0 < x * z := by
    nlinarith
  have hyz : 0 < y * z := by
    nlinarith
  have h4 : 0 < (1 + x) * (1 + y) * (1 + z) := by
    positivity
  have h5 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 =
      (x ^ 3 * (1 + x) + y ^ 3 * (1 + y) + z ^ 3 * (1 + z) - 3 / 4 * ((1 + x) * (1 + y) * (1 + z)) ) / ((1 + x) * (1 + y) * (1 + z)) := by
    field_simp
    ring
  have h6 : x ^ 3 * (1 + x) + y ^ 3 * (1 + y) + z ^ 3 * (1 + z) - 3 / 4 * ((1 + x) * (1 + y) * (1 + z)) ≥ 0 := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      hxyz,
      mul_pos hx hy, 
      mul_pos hy hz, 
      mul_pos hx hz
     ]
  have h7 : (x ^ 3 * (1 + x) + y ^ 3 * (1 + y) + z ^ 3 * (1 + z) - 3 / 4 * ((1 + x) * (1 + y) * (1 + z)) ) ≥ 0 := by
    linarith [h6]
  have h8 : (x ^ 3 * (1 + x) + y ^ 3 * (1 + y) + z ^ 3 * (1 + z) - 3 / 4 * ((1 + x) * (1 + y) * (1 + z)) ) / ((1 + x) * (1 + y) * (1 + z)) ≥ 0 := by
    apply div_nonneg
    linarith [h6]
    all_goals nlinarith
  linarith [h5, h8]