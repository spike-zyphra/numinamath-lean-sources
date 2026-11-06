import Mathlib

theorem inequalities_89971 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a + b + c ≤ b * c / (b + c) + c * a / (c + a) + a * b / (a + b) +
    (b * c / a + c * a / b + a * b / c) / 2 := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < c := hc
  have h4 : 0 < a * b * c := by
    positivity
  have h5 : 0 < b + c := by
    linarith
  have h6 : 0 < c + a := by
    linarith
  have h7 : 0 < a + b := by
    linarith
  have h11 : (b * c / (b + c) + c * a / (c + a) + a * b / (a + b) +
      (b * c / a + c * a / b + a * b / c) / 2) - (a + b + c) ≥ 0 := by
    have h12 : (b * c / (b + c) + c * a / (c + a) + a * b / (a + b) +
        (b * c / a + c * a / b + a * b / c) / 2) - (a + b + c) =
        (2 * b * c * a * b * c * (c + a) * (a + b) + 2 * c * a * a * b * c * (b + c) * (a + b) +
         2 * a * b * a * b * c * (b + c) * (c + a) +
         b * c * b * c * (b + c) * (c + a) * (a + b) + c * a * a * c * (b + c) * (c + a) * (a + b) + a * b * a * b * (b + c) * (c + a) * (a + b) - 2 * (a + b + c) * a * b * c * (b + c) * (c + a) * (a + b)
        ) / (2 * a * b * c * (b + c) * (c + a) * (a + b))
      := by
        field_simp
        ring
    rw [h12]
    apply div_nonneg
    have h9 : 2 * b * c * a * b * c * (c + a) * (a + b) + 2 * c * a * a * b * c * (b + c) * (a + b) +
        2 * a * b * a * b * c * (b + c) * (c + a) +
        b * c * b * c * (b + c) * (c + a) * (a + b) + c * a * a * c * (b + c) * (c + a) * (a + b) + a * b * a * b * (b + c) * (c + a) * (a + b) - 2 * (a + b + c) * a * b * c * (b + c) * (c + a) * (a + b) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
        sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (b * c - c * a),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
              mul_pos (show 0 < a * b by nlinarith) (show 0 < c * a by nlinarith), 
                mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith),
                  sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)),
                    sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)),
                      sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)),
                        mul_pos ha (show 0 < a * b by nlinarith), 
                          mul_pos ha (show 0 < b * c by nlinarith), 
                            mul_pos ha (show 0 < c * a by nlinarith), 
                              mul_pos hb (show 0 < a * b by nlinarith), 
                                mul_pos hb (show 0 < b * c by nlinarith), 
                                  mul_pos hb (show 0 < c * a by nlinarith), 
                                    mul_pos hc (show 0 < a * b by nlinarith), 
                                      mul_pos hc (show 0 < b * c by nlinarith), 
                                        mul_pos hc (show 0 < c * a by nlinarith)]
    linarith [h9]
    all_goals
      positivity
  linarith [h11]