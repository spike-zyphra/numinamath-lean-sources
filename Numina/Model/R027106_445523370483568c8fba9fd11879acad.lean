import Mathlib

theorem inequalities_248191 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ((2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) + (2 * b + c + a)^2 / (2 * b^2 + (c + a)^2) +
     (2 * c + a + b)^2 / (2 * c^2 + (a + b)^2)) ≤ 8 := by

  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < a * c := mul_pos ha hc
  have h3 : 0 < b * c := mul_pos hb hc
  have h4 : (2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) + (2 * b + c + a)^2 / (2 * b^2 + (c + a)^2) + (2 * c + a + b)^2 / (2 * c^2 + (a + b)^2) - 8 ≤ 0 := by
    have h5 : 0 < 2 * a^2 + (b + c) ^ 2 := by
      positivity
    have h6 : 0 < 2 * b^2 + (c + a) ^ 2 := by
      positivity
    have h7 : 0 < 2 * c^2 + (a + b) ^ 2 := by
      positivity
    have h8 : (2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) + (2 * b + c + a)^2 / (2 * b^2 + (c + a)^2) + (2 * c + a + b)^2 / (2 * c^2 + (a + b)^2) - 8 ≤ 0 := by
      have h5 : 0 < (2 * a^2 + (b + c) ^ 2) * (2 * b^2 + (c + a) ^ 2) * (2 * c^2 + (a + b) ^ 2) := by positivity
      have h9 : (2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) + (2 * b + c + a)^2 / (2 * b^2 + (c + a)^2) + (2 * c + a + b)^2 / (2 * c^2 + (a + b)^2) - 8 =
          ((2 * a + b + c)^2 * (2 * b^2 + (c + a)^2) * (2 * c^2 + (a + b)^2) + (2 * b + c + a)^2 * (2 * a^2 + (b + c)^2) * (2 * c^2 + (a + b)^2) + (2 * c + a + b)^2 * (2 * a^2 + (b + c)^2) * (2 * b^2 + (c + a)^2) - 8 * (2 * a^2 + (b + c)^2) * (2 * b^2 + (c + a)^2) * (2 * c^2 + (a + b)^2)) / ((2 * a^2 + (b + c) ^ 2) * (2 * b^2 + (c + a) ^ 2) * (2 * c^2 + (a + b) ^ 2)) := by
        field_simp
        ring
      rw [h9]
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show numerator is nonpositive
        nlinarith [sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c), 
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < a * b from by positivity) (show 0 < a * c from by positivity), 
          mul_pos (show 0 < a * b from by positivity) (show 0 < b * c from by positivity), 
          mul_pos (show 0 < a * c from by positivity) (show 0 < b * c from by positivity)
      ]
      all_goals positivity
    linarith 
  linarith