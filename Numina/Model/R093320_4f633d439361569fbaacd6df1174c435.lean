import Mathlib

open Real

theorem inequalities_314363 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 ≤ 1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) := by 
  have h1 : 0 < (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) := by 
    apply mul_pos
    apply mul_pos
    all_goals 
      nlinarith 
  have h2 : 1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) - 1 ≥ 0 := by 
    have h3 : (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) > 0 := by 
      positivity 
    have h4 : (1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) - 1) = 
      ((1 + 2 * b) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * b) - (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c)) / ((1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c)) := by 
      field_simp 
      <;> ring 
    rw [h4] 
    have h5 : (1 + 2 * b) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * b) - (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) ≥ 0 := by 
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1), 
                  sq_nonneg (a * b * c - 1), 
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc 
                ]
    apply div_nonneg 
    linarith 
    all_goals nlinarith 
  linarith