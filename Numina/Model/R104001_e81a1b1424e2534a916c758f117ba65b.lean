import Mathlib

theorem inequalities_34109 (a b c : ℝ) (h₀ : a > b) (h₁ : b > c) :
    1 / (a - b) + 1 / (b - c) > 2 / (a - c) := by
  have hab : a - b > 0 := sub_pos.mpr h₀
  have hbc : b - c > 0 := sub_pos.mpr h₁
  have hac : a - c > 0 := by linarith

  have h2 : (b - c) * (a - c) + (a - b) * (a - c) - 2 * (a - b) * (b - c) > 0 := by
    nlinarith [sq_pos_of_pos hbc, sq_pos_of_pos hab, sq_pos_of_pos (show a - c > 0 by linarith), sq_nonneg (a - b - c), sq_nonneg (b - c), sq_nonneg (a - c - b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

  have h3 : (1 / (a - b) + 1 / (b - c) - 2 / (a - c)) > 0 := by
    have h4 : (1 / (a - b) + 1 / (b - c) - 2 / (a - c)) =
        (( (b - c) * (a - c) + (a - b) * (a - c) - 2 * (a - b) * (b - c) )) / (( (a - b) * (b - c) * (a - c) )) := by
      field_simp [ne_of_gt hbc, ne_of_gt hab, ne_of_gt hac]
      ring
    rw [h4]
    apply div_pos
    linarith
    -- Show denominator is positive
    positivity

  linarith