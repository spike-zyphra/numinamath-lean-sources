import Mathlib

theorem inequalities_142460 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x ^ 2 / y ^ 2 + y ^ 2 / z ^ 2 + z ^ 2 / x ^ 2 ≥ x / z + z / y + y / x := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz
  
  have h2 : x ^ 2 / y ^ 2 + y ^ 2 / z ^ 2 + z ^ 2 / x ^ 2 - (x / z + z / y + y / x) ≥ 0 := by
    have h3 : 0 < x ^ 2 * y ^ 2 * z ^ 2 := by
      positivity
    have h4 : x ^ 4 * z ^ 2 + x ^ 2 * y ^ 4 + y ^ 2 * z ^ 4 ≥ x ^ 3 * y ^ 2 * z + x ^ 2 * z ^ 3 * y + x * y ^ 3 * z ^ 2 := by
      nlinarith [sq_nonneg (x ^ 2 * z - x * y ^ 2), sq_nonneg (x * y ^ 2 - y * z ^ 2), sq_nonneg (y * z ^ 2 - x ^ 2 * z), sq_nonneg (x ^ 2 * y - x * z ^ 2), sq_nonneg (x * y ^ 3 - x ^ 3 * z), sq_nonneg (y * z - x * y), sq_nonneg (x ^ 2 * z ^ 2), sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (z ^ 2 - x ^ 2), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    
    have eq : (x ^ 2 / y ^ 2 + y ^ 2 / z ^ 2 + z ^ 2 / x ^ 2 - (x / z + z / y + y / x)) =
          (x ^ 4 * z ^ 2 + x ^ 2 * y ^ 4 + y ^ 2 * z ^ 4 - (x ^ 3 * y ^ 2 * z + x ^ 2 * z ^ 3 * y + x * y ^ 3 * z ^ 2)) / (x ^ 2 * y ^ 2 * z ^ 2) := by
      field_simp
      ring
    rw [eq]
    apply div_nonneg
    linarith
    all_goals positivity
  linarith