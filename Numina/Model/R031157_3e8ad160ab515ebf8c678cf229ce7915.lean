import Mathlib

theorem inequalities_55795 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / b + b / c + c / a ≥ (c + a) / (c + b) + (a + b) / (a + c) + (b + c) / (b + a) := by
  have h1 : 0 < a * b * c := by
    positivity

  have h2 : 0 < (c + b) * (a + c) * (b + a) := by
    positivity
  
  have h3 : 0 < a * b * c * (c + b) * (a + c) * (b + a) := by
    positivity
  
  have h4 : a / b + b / c + c / a - ((c + a) / (c + b) + (a + b) / (a + c) + (b + c) / (b + a)) ≥ 0 := by 
    have h5 : 0 < a * b * c * (c + b) * (a + c) * (b + a) := by positivity

    have h7 : a / b + b / c + c / a - ((c + a) / (c + b) + (a + b) / (a + c) + (b + c) / (b + a)) =
      (a^2 * c * (c + b) * (a + c) * (b + a) +
        b^2 * a * (c + b) * (a + c) * (b + a) +
        c^2 * b * (c + b) * (a + c) * (b + a) -
        (c + a) * (a * b * c * (a + c) * (b + a)) -
        (a + b) * (a * b * c * (c + b) * (b + a)) -
        (b + c) * (a * b * c * (c + b) * (a + c))
      ) / (a * b * c * (c + b) * (a + c) * (b + a)) := by 
      field_simp
      ring

    rw [h7]

    apply div_nonneg
    -- To prove that the numerator is non-negative
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
        mul_pos (show 0 < c + b by linarith) (show 0 < a + c by linarith),
        mul_pos (show 0 < c + b by linarith) (show 0 < b + a by linarith),
        mul_pos (show 0 < a + c by linarith) (show 0 < b + a by linarith)]
  
    all_goals 
      positivity
  
  linarith [h4]