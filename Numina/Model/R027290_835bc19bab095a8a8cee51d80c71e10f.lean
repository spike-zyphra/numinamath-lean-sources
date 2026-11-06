import Mathlib

theorem inequalities_3896 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * b ^ 3 / c + b * c ^ 3 / a + c * a ^ 3 / b + 3 * a * b * c ≥
    2 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) := by
  have h1 : 0 < a * b * c := by positivity
  have h2 : a * b ^ 3 / c + b * c ^ 3 / a + c * a ^ 3 / b + 3 * a * b * c - 2 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ≥ 0 := by
    have pos1 : 0 < a * b * c := by positivity
    have h3 : a * b ^ 3 / c + b * c ^ 3 / a + c * a ^ 3 / b + 3 * a * b * c - 2 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) =
        (a ^ 2 * b ^ 4 + b ^ 2 * c ^ 4 + c ^ 2 * a ^ 4 + 3 * (a * b * c) ^ 2 - 2 * (a^3 * b^2 * c + a * b^3 * c^2 + a^2 * b * c^3)) / (a * b * c) := by
      field_simp
      ring
    rw [h3]
    have h4 : a ^ 2 * b ^ 4 + b ^ 2 * c ^ 4 + c ^ 2 * a ^ 4 + 3 * (a * b * c) ^ 2 - 2 * (a^3 * b^2 * c + a * b^3 * c^2 + a^2 * b * c^3) ≥ 0 := by
      nlinarith [sq_nonneg (a * b ^ 2 - b * c ^ 2), sq_nonneg (b * c ^ 2 - c * a ^ 2), sq_nonneg (c * a ^ 2 - a * b ^ 2), 
            sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
            sq_nonneg (a^2 * b - b^2 * c), sq_nonneg (b^2 * c - c^2 * a), sq_nonneg (c^2 * a - a^2 * b), 
            sq_nonneg (a * b^2 - b * c^2), sq_nonneg (b * c^2 - c * a^2), sq_nonneg (c * a^2 - a * b^2), 
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
            mul_pos (show 0 < a * b from by positivity) (show 0 < b * c from by positivity), 
            mul_pos (show 0 < a * b from by positivity) (show 0 < c * a from by positivity), 
            mul_pos (show 0 < b * c from by positivity) (show 0 < c * a from by positivity)
        ]
    have h5 : 0 < a * b * c := by positivity
    have h6 : (a ^ 2 * b ^ 4 + b ^ 2 * c ^ 4 + c ^ 2 * a ^ 4 + 3 * (a * b * c) ^ 2 - 2 * (a^3 * b^2 * c + a * b^3 * c^2 + a^2 * b * c^3)) / (a * b * c) ≥ 0 := by 
      apply div_nonneg
      linarith [h4]
      all_goals
      positivity
    linarith [h6]
  linarith [h2]