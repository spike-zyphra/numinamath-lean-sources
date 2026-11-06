import Mathlib

theorem inequalities_602866 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    a / (1 + a) + b / (1 + b) < 1 / (1 + a * b) := by

  have hb1 : b = 1 - a := by linarith
  have h1 : 0 < 1 + a := by linarith
  have h2 : 0 < 1 + b := by
    rw [hb1]
    linarith
  have h3 : 0 < 1 + a * b := by
    nlinarith [h, mul_pos ha hb]

  have h4 : a / (1 + a) + b / (1 + b) - 1 / (1 + a * b) < 0 := by
    have pos1 : 0 < (1 + a) * (1 + b) * (1 + a * b) := by positivity
    have h5 : a / (1 + a) + b / (1 + b) - 1 / (1 + a * b) =
        ( (a * (1 + b) * (1 + a * b) + b * (1 + a) * (1 + a * b) - (1 + a) * (1 + b) ) / ( (1 + a) * (1 + b) * (1 + a * b) ) ) := by 
      field_simp [show 0 < 1 + a by linarith, show 0 < 1 + b by 
        rw [hb1]
        linarith, show 0 < 1 + a * b by nlinarith [h, mul_pos ha hb]
        ]
      ring
    rw [h5] at *
    apply div_neg_of_neg_of_pos
    · 
      rw [hb1]
      nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg ((1 - a) - 1 / 2), mul_pos ha (show 0 < 1 - a by nlinarith), sq_nonneg (a * (1 - a)), sq_nonneg ((a - 1/2) * (a - 1/2)), sq_nonneg ((a - 1/2) * (1 - a)), sq_pos_of_pos (show 0 < a * (1 - a) by nlinarith) ]
    · positivity
  
  linarith [h4]
  all_goals linarith