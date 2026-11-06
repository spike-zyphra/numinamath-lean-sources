import Mathlib

open Real

theorem inequalities_266942 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1) :
    2 ≤ (x ^ 2 + y ^ 2) / z + (y ^ 2 + z ^ 2) / x + (z ^ 2 + x ^ 2) / y := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz
  
  have h2 : (x ^ 2 + y ^ 2) / z + (y ^ 2 + z ^ 2) / x + (z ^ 2 + x ^ 2) / y - 2 ≥ 0 := by
    have pos1 : 0 < x * y * z := by
      apply mul_pos
      apply mul_pos
      exact hx
      exact hy
      exact hz

    have h3 : (x ^ 2 + y ^ 2) / z + (y ^ 2 + z ^ 2) / x + (z ^ 2 + x ^ 2) / y - 2 =
        ((x ^ 2 + y ^ 2) * (x * y) + (y ^ 2 + z ^ 2) * (y * z) + (z ^ 2 + x ^ 2) * (x * z) - 2 * (x * y * z)) / (x * y * z) := by
      field_simp
      ring
    rw [h3]

    have h4 : ((x ^ 2 + y ^ 2) * (x * y) + (y ^ 2 + z ^ 2) * (y * z) + (z ^ 2 + x ^ 2) * (x * z) - 2 * (x * y * z)) ≥ 0 := by
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
        sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), 
        sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), 
        sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

    have pos2 : (x * y * z) > 0 := by
      apply mul_pos
      apply mul_pos
      exact hx
      exact hy
      exact hz

    apply div_nonneg
    linarith
    all_goals positivity

  linarith