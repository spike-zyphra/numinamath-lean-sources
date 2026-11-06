import Mathlib

theorem inequalities_71816 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 4 ≤ a ^ 2 / (a + b) ^ 2 + b ^ 2 / (b + c) ^ 2 + c ^ 2 / (c + a) ^ 2 := by
  have h3 : a ^ 2 / (a + b) ^ 2 + b ^ 2 / (b + c) ^ 2 + c ^ 2 / (c + a) ^ 2 - 3 / 4 ≥ 0 := by
    have pos1 : 0 < (a + b) ^ 2 := by positivity
    have pos2 : 0 < (b + c) ^ 2 := by positivity
    have pos3 : 0 < (c + a) ^ 2 := by positivity
    have h4 : a ^ 2 / (a + b) ^ 2 + b ^ 2 / (b + c) ^ 2 + c ^ 2 / (c + a) ^ 2 - 3 / 4 =
            (4 * a^2 * (b+c)^2 * (c+a)^2 + 4 * b^2 * (a+b)^2 * (c+a)^2 + 4 * c^2 * (a+b)^2 * (b+c)^2 - 3 * (a+b)^2 * (b+c)^2 * (c+a)^2) / (4 * (a+b)^2 * (b+c)^2 * (c+a)^2) := by 
      field_simp
      ring 
    rw [h4] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), 
          sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), 
          sq_nonneg (c - a), sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]
    all_goals
      positivity
  linarith