import Mathlib

theorem inequalities_318383 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z = 1) :
    1 < (1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z)) ∧
    (1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z)) < 2 := by
  constructor
  · -- Prove that 1 < 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z)
    have h1 : 0 < (1 + x) * (1 + y) * (1 + z) := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h2 : (1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) ) - 1 > 0 := by
      have h3 : (1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) ) - 1 =
          ( (1 * (1 + y) * (1 + z) + 1 * (1 + x) * (1 + z) + 1 * (1 + x) * (1 + y) - (1 + x) * (1 + y) * (1 + z) ) / ( (1 + x) * (1 + y) * (1 + z) ) ) := by
        field_simp
        <;> ring
      rw [h3]
      apply div_pos
      · -- Show that numerator > 0
        nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
          h, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
      · -- Show that denominator > 0
        positivity
    linarith
  · -- Prove that 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) < 2
    have h1 : 0 < (1 + x) * (1 + y) * (1 + z) := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h2 : (1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) ) - 2 < 0 := by
      have h3 : (1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) ) - 2 =
          ( (1 * (1 + y) * (1 + z) + 1 * (1 + x) * (1 + z) + 1 * (1 + x) * (1 + y) - 2 * ( (1 + x) * (1 + y) * (1 + z) ) ) / ( (1 + x) * (1 + y) * (1 + z) ) ) := by
        field_simp
        <;> ring
      rw [h3]
      apply div_neg_of_neg_of_pos
      · -- Show that numerator is negative
        nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
          h, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
      · -- Show that denominator > 0
        positivity
    linarith