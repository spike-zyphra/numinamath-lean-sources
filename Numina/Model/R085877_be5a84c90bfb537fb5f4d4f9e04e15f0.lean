import Mathlib

theorem inequalities_308118 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z = 1) :
    1 < 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) ∧
    1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) < 2 := by
  have hx1 : 0 < (1 + x) := by linarith
  have hy1 : 0 < (1 + y) := by linarith
  have hz1 : 0 < (1 + z) := by linarith

  have hxyz1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  rw [h] at hxyz1

  constructor
  · -- Prove the lower bound: 1 < 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z)
    have h1 : 1 < 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) := by
      have h6 : 0 < (1 + x) * (1 + y) * (1 + z) := by
          positivity

      have h7 : (1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) - 1) > 0 := by
        have h8 : (1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) - 1) =
            ((1 + y) * (1 + z) + (1 + x) * (1 + z) + (1 + x) * (1 + y) - (1 + x) * (1 + y) * (1 + z)) / ((1 + x) * (1 + y) * (1 + z)) := by
          field_simp
          ring

        rw [h8]

        apply div_pos
        nlinarith [sq_nonneg (x * y - x * z), sq_nonneg (y * x - y * z), sq_nonneg (z * x - z * y),
           sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z),
           mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
           hxyz1]
        all_goals positivity

      linarith

    linarith [h1]

  · -- Prove the upper bound: 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) < 2
    have h2 : 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) < 2 := by
      have h6 : 0 < (1 + x) * (1 + y) * (1 + z) := by
          positivity

      have h8 : (2 - (1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z))) > 0 := by
        have h9 : (2 - (1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z))) =
            ((2 * (1 + x) * (1 + y) * (1 + z) - ((1 + y) * (1 + z) + (1 + x) * (1 + z) + (1 + x) * (1 + y))) / ((1 + x) * (1 + y) * (1 + z))) := by
          field_simp
          ring

        rw [h9]

        apply div_pos
        nlinarith [sq_nonneg (x * y - x * z), sq_nonneg (y * x - y * z), sq_nonneg (z * x - z * y),
           sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z),
           mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
           hxyz1]
        all_goals positivity

      linarith

    linarith [h2]