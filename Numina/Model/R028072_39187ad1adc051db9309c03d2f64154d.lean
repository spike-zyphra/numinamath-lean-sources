import Mathlib

theorem inequalities_57390 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b ≥ 1) :
    (a + 2 * b + 2 / (a + 1)) * (b + 2 * a + 2 / (b + 1)) ≥ 16 := by
  have h1 : 0 < a + 1 := by linarith
  have h2 : 0 < b + 1 := by linarith

  have h3 : (a + 2 * b + 2 / (a + 1)) * (b + 2 * a + 2 / (b + 1)) - 16 ≥ 0 := by

    have h5 : (a + 2 * b + 2 / (a + 1)) * (b + 2 * a + 2 / (b + 1)) - 16 =
        (((a + 2 * b) * (a + 1) + 2) * ((b + 2 * a) * (b + 1) + 2) - 16 * ((a + 1) * (b + 1))) / ((a + 1) * (b + 1)) := by
      field_simp
      <;> ring
    rw [h5]

    have h6 : (((a + 2 * b) * (a + 1) + 2) * ((b + 2 * a) * (b + 1) + 2) - 16 * ((a + 1) * (b + 1))) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), 
          sq_nonneg (a - b), sq_nonneg (a * (a - 1)), sq_nonneg (b * (b - 1)), 
          mul_pos ha hb, mul_pos ha (show 0 < b + 1 by linarith), 
          mul_pos hb (show 0 < a + 1 by linarith)
          ]
    apply div_nonneg h6 (by positivity)
  linarith