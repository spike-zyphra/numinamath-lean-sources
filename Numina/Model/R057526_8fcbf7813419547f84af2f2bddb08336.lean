import Mathlib

theorem inequalities_598319 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by 
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : 0 < (b + c) * (c + a) * (a + b) := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h3 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h4 : (a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2) =
        (2 * (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a)) - 3 * (b + c) * (c + a) * (a + b)) / (2 * (b + c) * (c + a) * (a + b)) := by
      field_simp
      ring
    rw [h4]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
              sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
              sq_nonneg (b * (b - c)), sq_nonneg (c * (a - b)), 
              sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), 
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    positivity
  linarith