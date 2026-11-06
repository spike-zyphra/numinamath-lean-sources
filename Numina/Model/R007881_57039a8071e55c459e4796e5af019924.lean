import Mathlib

theorem inequalities_262220 (a b : ℝ) (ha : a > 1) (hb : b > 1) :
    8 ≤ a^2 / (b - 1) + b^2 / (a - 1) := by
  have ha1 : a - 1 > 0 := by linarith
  have hb1 : b - 1 > 0 := by linarith
  have h0 : a^2 / (b - 1) + b^2 / (a - 1) - 8 ≥ 0 := by 
    have h1 : a^2 / (b - 1) + b^2 / (a - 1) - 8 =
      (a^2 * (a - 1) + b^2 * (b - 1) - 8 * (b - 1) * (a - 1)) / ((b - 1) * (a - 1)) := by
      field_simp [hb1, ha1]
      <;> ring
    have h2 : a^2 * (a - 1) + b^2 * (b - 1) - 8 * (b - 1) * (a - 1) ≥ 0 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 4), 
          sq_nonneg (a - 2), sq_nonneg (b - 2),
          sq_nonneg (a - 1), sq_nonneg (b - 1), 
          mul_pos ha1 hb1, 
          mul_nonneg (show (0 : ℝ) ≤ a - 1 by linarith) 
          (show (0 : ℝ) ≤ b - 1 by linarith)
      ]
    have h4 : 0 < (b - 1) * (a - 1) := mul_pos hb1 ha1
    rw [h1]
    apply div_nonneg 
    linarith 
    positivity
  linarith