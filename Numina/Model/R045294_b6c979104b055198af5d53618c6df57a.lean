import Mathlib

theorem inequalities_600086 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    3 / 4 ≤ x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) +
    z ^ 3 / ((1 + x) * (1 + y)) := by 
  have hx1 : 0 < x := hx
  have hy1 : 0 < y := hy
  have hz1 : 0 < z := hz
  have h1 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 ≥ 0 := by
    have pos1 : (1 + y) * (1 + z) * (1 + x) > 0 := by positivity
    have h2 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 =
        ( (x ^ 3 * (1 + x) + y ^ 3 * (1 + y) + z ^ 3 * (1 + z) - 3 / 4 * ( (1 + y) * (1 + z) * (1 + x) )) / ((1 + y) * (1 + z) * (1 + x)) ) := by 
      field_simp 
      ring
    rw [h2] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
      hxyz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz 
    ]
    all_goals positivity
  linarith