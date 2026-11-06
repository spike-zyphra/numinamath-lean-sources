import Mathlib

theorem inequalities_599264 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a * (1 - b) + b = 1) :
    a ^ 2 / (a + 1) + b ^ 2 / (b + 1) ≥ 1 / 3 := by 
  have h1 : a * b = a + b - 1 := by
    linarith
  have h2 : 0 < a * b := by
    nlinarith
  have h3 : a ^ 2 / (a + 1) + b ^ 2 / (b + 1) - 1 / 3 ≥ 0 := by 
    have pos1 : 0 < (a + 1) * (b + 1) * 3 := by positivity
    have h4 : a ^ 2 / (a + 1) + b ^ 2 / (b + 1) - 1 / 3 =
      (3 * (a ^ 2 * (b + 1) + b ^ 2 * (a + 1)) - (a + 1) * (b + 1)) / ((a + 1) * (b + 1) * 3) := by 
      field_simp 
      <;> ring 
    rw [h4] at *
    apply div_nonneg 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a * b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), mul_pos ha hb, h, h1]
    all_goals 
      positivity 
  linarith