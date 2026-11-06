import Mathlib

theorem inequalities_601266
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (habc : a * b * c = 1) :
    a / b + b / c + c / a ≥ a + b + c := by

  have h1 : 0 < a * b * c := by positivity
  have h2 : a / b + b / c + c / a - (a + b + c) ≥ 0 := by
    have h3 : a / b + b / c + c / a - (a + b + c) = (a^2 * c + a * b^2 + b * c^2 - (a + b + c) * (a * b * c)) / (a * b * c) := by 
      field_simp
      ring
    rw [h3]
    have h4 : 0 < a * b * c := by positivity
    apply div_nonneg 
    have h5 : a^2 * c + a * b^2 + b * c^2 - (a + b + c) * (a * b * c) ≥ 0 := by
      have h6 : a * b * c = 1 := habc
      have eq1 : a^2 * c + a * b^2 + b * c^2 ≥ a + b + c := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), 
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
              mul_pos (show 0 < a by linarith) (show 0 < b by linarith), 
                mul_pos (show 0 < a by linarith) (show 0 < c by linarith), 
                  mul_pos (show 0 < b by linarith) (show 0 < c by linarith), 
                    mul_pos (show 0 < a * b by nlinarith) (show 0 < c by linarith)
        ]
      have eq3 : a^2 * c + a * b^2 + b * c^2 - (a + b + c) * (a * b * c) = (a^2 * c + a * b^2 + b * c^2) - (a + b + c) := by
        rw [show (a * b * c) = 1 by linarith [h6]]
        all_goals linarith
      nlinarith
    linarith 
    positivity
  linarith