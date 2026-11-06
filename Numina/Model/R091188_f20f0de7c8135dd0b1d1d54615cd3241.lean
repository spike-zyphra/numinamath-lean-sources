import Mathlib

theorem inequalities_312287 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x ^ 3 / (y * z) + y ^ 3 / (z * x) + z ^ 3 / (x * y) ≥ x + y + z := by
  have h_pos1 : 0 < y * z := by
    apply mul_pos
    all_goals assumption
  have h_pos2 : 0 < z * x := by
    apply mul_pos
    all_goals assumption
  have h_pos3 : 0 < x * y := by
    apply mul_pos
    all_goals assumption

  have h1 : x ^ 3 / (y * z) + y ^ 3 / (z * x) + z ^ 3 / (x * y) - (x + y + z) ≥ 0 := by
    have h_pos4 : 0 < x * y * z := by
      apply mul_pos
      apply mul_pos
      all_goals assumption

    have h2 : x ^ 3 / (y * z) + y ^ 3 / (z * x) + z ^ 3 / (x * y) - (x + y + z) =
      (x ^ 4 + y ^ 4 + z ^ 4 - (x + y + z) * (x * y * z)) / (x * y * z) := by
      field_simp [h_pos1, h_pos2, h_pos3]
      ring
      <;> field_simp [h_pos1, h_pos2, h_pos3]
      <;> ring
      <;> field_simp [h_pos1, h_pos2, h_pos3]
      <;> ring
      <;> field_simp [h_pos1, h_pos2, h_pos3]
      <;> ring
      <;> field_simp [h_pos1, h_pos2, h_pos3]
      <;> ring
    rw [h2]

    apply div_nonneg
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (z ^ 2 - x ^ 2),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), 
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    
    positivity

  linarith [h1]