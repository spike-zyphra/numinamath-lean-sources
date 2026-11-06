import Mathlib

theorem algebra_100075 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a / (a + 1) + b / (b + 1) = 1) :
    a / (b ^ 2 + 1) - b / (a ^ 2 + 1) = a - b := by

  have h1 : a * b = 1 := by
    have h2 : a + 1 ≠ 0 := by
      linarith
    have h3 : b + 1 ≠ 0 := by
      linarith
    field_simp [h2, h3] at h
    nlinarith
    all_goals linarith

  have h2 : b = 1 / a := by
    have h3 : a ≠ 0 := by
      linarith
    field_simp
    nlinarith [h1]

  rw [h2]
  have h3 : a * (1 / a) = 1 := by
    have h4 : a ≠ 0 := by
      nlinarith
    field_simp
    all_goals linarith

  field_simp [(show a ≠ 0 by linarith), (show (1 / a : ℝ) ^ 2 + 1 ≠ 0 by
    positivity
  ), (show a ^ 2 + 1 ≠ 0 by
    positivity
  )]
  <;> nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, h1, sq_nonneg (a - 1), sq_nonneg (a * b - 1)]