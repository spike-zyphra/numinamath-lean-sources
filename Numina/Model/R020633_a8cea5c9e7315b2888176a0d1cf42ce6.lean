import Mathlib

theorem inequalities_279105 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    3 / 5 ≤ (x + y - z) ^ 2 / ((x + y) ^ 2 + z ^ 2) +
            (y + z - x) ^ 2 / ((y + z) ^ 2 + x ^ 2) +
            (z + x - y) ^ 2 / ((z + x) ^ 2 + y ^ 2) := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have pos1 : (x + y) ^ 2 + z ^ 2 > 0 := by positivity
  have pos2 : (y + z) ^ 2 + x ^ 2 > 0 := by positivity
  have pos3 : (z + x) ^ 2 + y ^ 2 > 0 := by positivity
  have h2 : (x + y - z) ^ 2 / ((x + y) ^ 2 + z ^ 2) + (y + z - x) ^ 2 / ((y + z) ^ 2 + x ^ 2) + (z + x - y) ^ 2 / ((z + x) ^ 2 + y ^ 2) - 3 / 5 ≥ 0 := by 
    have pos1 : (x + y) ^ 2 + z ^ 2 > 0 := by positivity
    have pos2 : (y + z) ^ 2 + x ^ 2 > 0 := by positivity
    have pos3 : (z + x) ^ 2 + y ^ 2 > 0 := by positivity
    have h3 : (x + y - z) ^ 2 / ((x + y) ^ 2 + z ^ 2) + (y + z - x) ^ 2 / ((y + z) ^ 2 + x ^ 2) + (z + x - y) ^ 2 / ((z + x) ^ 2 + y ^ 2) - 3 / 5 =
          ((x + y - z) ^ 2 * ((y + z) ^ 2 + x ^ 2) * ((z + x) ^ 2 + y ^ 2) +
          (y + z - x) ^ 2 * ((x + y) ^ 2 + z ^ 2) * ((z + x) ^ 2 + y ^ 2) +
          (z + x - y) ^ 2 * ((x + y) ^ 2 + z ^ 2) * ((y + z) ^ 2 + x ^ 2) -

          (3 / 5) * ((x + y) ^ 2 + z ^ 2) * ((y + z) ^ 2 + x ^ 2) * ((z + x) ^ 2 + y ^ 2)) / (( (x + y) ^ 2 + z ^ 2) * ((y + z) ^ 2 + x ^ 2) * ((z + x) ^ 2 + y ^ 2)) := by 
      field_simp
      <;> ring
    rw [h3]
    apply div_nonneg
    -- Prove that the numerator is non-negative
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
          sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)),
          sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
          ]
    -- Prove that the denominator is positive
    positivity

  linarith