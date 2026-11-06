import Mathlib

theorem inequalities_111059 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    1 < 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) ∧
    1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) < 2 := by
  have h1 : 0 < (1 + x) * (1 + y) * (1 + z) := by
    positivity
  constructor
  · -- Prove 1 < 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z)
    have h2 : 1 < 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) := by
      have pos1 : 0 < (1 + x) * (1 + y) * (1 + z) := by positivity
      have h3 : 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) - 1 > 0 := by
        have pos2 : 0 < (1 + x) * (1 + y) * (1 + z) := by positivity
        have h4 : 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) - 1 =
            ((1 + y) * (1 + z) + (1 + x) * (1 + z) + (1 + x) * (1 + y) - (1 + x) * (1 + y) * (1 + z)) / ((1 + x) * (1 + y) * (1 + z)) := by
          field_simp
          <;> ring
        rw [h4] at *
        apply div_pos
        -- Show the numerator is positive
        nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x * z - 1), sq_nonneg (y * z - 1),
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          hxyz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
        all_goals positivity
      linarith
    linarith
  · -- Prove 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) < 2
    have h3 : 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) < 2 := by
      have pos1 : 0 < (1 + x) * (1 + y) * (1 + z) := by positivity
      have h4 : 2 - (1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z)) > 0 := by
        have pos2 : 0 < (1 + x) * (1 + y) * (1 + z) := by positivity
        have h5 : 2 - (1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z)) =
            (2 * (1 + x) * (1 + y) * (1 + z) - ((1 + y) * (1 + z) + (1 + x) * (1 + z) + (1 + x) * (1 + y))) / ((1 + x) * (1 + y) * (1 + z)) := by
          field_simp
          <;> ring
        rw [h5] at *
        apply div_pos
        -- Show the numerator is positive
        nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x * z - 1), sq_nonneg (y * z - 1),
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          hxyz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
        all_goals positivity
      linarith
    linarith