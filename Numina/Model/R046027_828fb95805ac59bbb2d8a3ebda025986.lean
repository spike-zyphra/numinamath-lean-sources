import Mathlib

theorem inequalities_5509 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    4 ≤ 2*a/(b+c) + 2*b/(c+a) + 2*c/(a+b) + (a*b+b*c+c*a)/(a^2+b^2+c^2) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc

  have h2 : 2 * a / (b + c) + 2 * b / (c + a) + 2 * c / (a + b) + (a * b + b * c + c * a) / (a^2 + b^2 + c^2) - 4 ≥ 0 := by
    have h3 : 0 < (b + c) * (c + a) * (a + b) * (a^2 + b^2 + c^2) := by
      positivity
    have h4 : 2 * a / (b + c) + 2 * b / (c + a) + 2 * c / (a + b) + (a * b + b * c + c * a) / (a^2 + b^2 + c^2) - 4 =
        ( (2 * a * (c + a) * (a + b) * (a^2 + b^2 + c^2) + 2 * b * (b + c) * (a + b) * (a^2 + b^2 + c^2) + 2 * c * (b + c) * (c + a) * (a^2 + b^2 + c^2) + (a * b + b * c + c * a) * (b + c) * (c + a) * (a + b) - 4 * (b + c) * (c + a) * (a + b) * (a^2 + b^2 + c^2) ) / ( (b + c) * (c + a) * (a + b) * (a^2 + b^2 + c^2) ) ) := by 
      field_simp
      ring
    rw [h4] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
          sq_nonneg (a * (a - b) + b * (b - a)), sq_nonneg (a * (a - c) + c * (c - a)), sq_nonneg (b * (b - c) + c * (c - b)), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < c * a by nlinarith), 
          mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith)
        ]
    all_goals
      positivity
  linarith [h2]