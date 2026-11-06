import Mathlib

theorem inequalities_596979 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (1 + a) ^ 3 + 1 / (1 + b) ^ 3 + 1 / (1 + c) ^ 3 +
    5 / ((1 + a) * (1 + b) * (1 + c)) ≥ 1 := by
  have h10 : 1 / (1 + a) ^ 3 + 1 / (1 + b) ^ 3 + 1 / (1 + c) ^ 3 + 5 / ((1 + a) * (1 + b) * (1 + c)) - 1 ≥ 0 := by
    have h11 : 0 < (1 + a) * (1 + b) * (1 + c) := by positivity
    have eq3 : 1 / (1 + a) ^ 3 + 1 / (1 + b) ^ 3 + 1 / (1 + c) ^ 3 + 5 / ((1 + a) * (1 + b) * (1 + c)) - 1 =
        ( (1 + b)^3 * (1 + c)^3 + (1 + a)^3 * (1 + c)^3 + (1 + a)^3 * (1 + b)^3
          + 5 * ( (1 + a) * (1 + b) * (1 + c) ) ^ 2 - ( (1 + a) ^3 * (1 + b) ^3 * (1 + c) ^3 ) ) 
        / ( (1 + a) ^3 * (1 + b) ^3 * (1 + c) ^3 ) := by 
      field_simp
      <;> ring
    rw [eq3] at *
    apply div_nonneg 
    · -- Show that the numerator is non-negative 
      have h11 : (1 + b)^3 * (1 + c)^3 + (1 + a)^3 * (1 + c)^3 + (1 + a)^3 * (1 + b)^3 + 5 * ((1 + a) * (1 + b) * (1 + c)) ^ 2 - ( (1 + a) ^3 * (1 + b) ^3 * (1 + c) ^3 ) ≥ 0 := by 
        have h2 : a * b * c = 1 := by linarith
        nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1), 
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          sq_nonneg (a * b * c - 1), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, h2, 
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), 
          sq_nonneg (a * b * c - 1)
        ]
      linarith 
    · -- Show that the denominator is positive 
      positivity 
  linarith