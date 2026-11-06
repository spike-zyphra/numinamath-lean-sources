import Mathlib

theorem inequalities_245678 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^3 + 3 * b^3) / (5 * a + b) + (b^3 + 3 * c^3) / (5 * b + c) +
    (c^3 + 3 * a^3) / (5 * c + a) ≥ 2 / 3 * (a^2 + b^2 + c^2) := by
  have hb1 : 0 < 5 * a + b := by
    nlinarith
  have hb2 : 0 < 5 * b + c := by
    nlinarith
  have hb3 : 0 < 5 * c + a := by
    nlinarith
  have h1 : (a^3 + 3 * b^3) / (5 * a + b) + (b^3 + 3 * c^3) / (5 * b + c) + 
    (c^3 + 3 * a^3) / (5 * c + a) - 2 / 3 * (a^2 + b^2 + c^2) ≥ 0 := by
    have hb4 : 0 < (5 * a + b) * (5 * b + c) * (5 * c + a) := by
      positivity
    have eq1 : (a^3 + 3 * b^3) / (5 * a + b) + (b^3 + 3 * c^3) / (5 * b + c) + 
      (c^3 + 3 * a^3) / (5 * c + a) - 2 / 3 * (a^2 + b^2 + c^2) =
      ((a^3 + 3 * b^3) * (5 * b + c) * (5 * c + a) + (b^3 + 3 * c^3) * (5 * a + b) * (5 * c + a) + 
      (c^3 + 3 * a^3) * (5 * a + b) * (5 * b + c) - (2/3)*(a^2 + b^2 + c^2) * ((5 * a + b) * (5 * b + c) * (5 * c + a)) ) / ((5 * a + b) * (5 * b + c) * (5 * c + a)) := by 
        field_simp 
        ring 
    have hb5 : ((a^3 + 3 * b^3) * (5 * b + c) * (5 * c + a) + (b^3 + 3 * c^3) * (5 * a + b) * (5 * c + a) + 
      (c^3 + 3 * a^3) * (5 * a + b) * (5 * b + c) - (2/3)*(a^2 + b^2 + c^2) * ((5 * a + b) * (5 * b + c) * (5 * c + a)) ) / ((5 * a + b) * (5 * b + c) * (5 * c + a)) ≥ 0 := by 
      have hb6 : (a^3 + 3 * b^3) * (5 * b + c) * (5 * c + a) + (b^3 + 3 * c^3) * (5 * a + b) * (5 * c + a) + (c^3 + 3 * a^3) * (5 * a + b) * (5 * b + c) - (2/3)*(a^2 + b^2 + c^2) * ((5 * a + b) * (5 * b + c) * (5 * c + a)) ≥ 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
          sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), 
          sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), 
          sq_nonneg (a * b - b * c), sq_nonneg (a * b - a * c), sq_nonneg (a * c - b * c), 
          mul_pos ha hb, 
          mul_pos ha hc, 
          mul_pos hb hc, 
          mul_pos ha (show 0 < a * b by nlinarith), 
          mul_pos ha (show 0 < a * c by nlinarith), 
          mul_pos hb (show 0 < b * c by nlinarith)
        ]
      apply div_nonneg 
      linarith 
      positivity 
    linarith
  linarith