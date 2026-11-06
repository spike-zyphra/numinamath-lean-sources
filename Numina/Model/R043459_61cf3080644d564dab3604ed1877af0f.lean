import Mathlib

theorem inequalities_137853 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z ≥ 1 / x + 1 / y + 1 / z) :
    x / y + y / z + z / x ≥ 1 / (x * y) + 1 / (y * z) + 1 / (z * x) := by
  have h1 : (x + y + z) * (x * y * z) ≥ (x * y + y * z + z * x) := by
    have hx2 : 0 < x * y * z := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h3 : (x + y + z) ≥ (1 / x + 1 / y + 1 / z) := h
    have h3' : (x + y + z) * (x * y * z) ≥ (1 / x + 1 / y + 1 / z) * (x * y * z) := by 
      apply mul_le_mul_of_nonneg_right
      linarith
      all_goals nlinarith
    have h4 : (1 / x + 1 / y + 1 / z) * (x * y * z) = (x * y + y * z + z * x) := by
      field_simp [hx.ne.symm, hy.ne.symm, hz.ne.symm]
      <;> ring
    nlinarith [h4]
  have h2 : x / y + y / z + z / x - (1 / (x * y) + 1 / (y * z) + 1 / (z * x)) ≥ 0 := by
    have h3 : x / y + y / z + z / x - (1 / (x * y) + 1 / (y * z) + 1 / (z * x)) =
        (x^2 * z + y^2 * x + z^2 * y - (x + y + z)) / (x * y * z) := by
      field_simp [hx.ne.symm, hy.ne.symm, hz.ne.symm]
      ring
    rw [h3]
    have hx2 : 0 < x * y * z := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h3 : x^2 * z + y^2 * x + z^2 * y ≥ x + y + z := by 
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx,
          h1
        ]
    apply div_nonneg 
    linarith 
    all_goals positivity 
  linarith