import Mathlib

theorem inequalities_598895 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 ≤ 1 / (a ^ 2 + a + 1) + 1 / (b ^ 2 + b + 1) + 1 / (c ^ 2 + c + 1) := by
  have h3 : 1 / (a ^ 2 + a + 1) + 1 / (b ^ 2 + b + 1) + 1 / (c ^ 2 + c + 1) - 1 ≥ 0 := by
    have h3_1 : 0 < a ^ 2 + a + 1 := by
      nlinarith [sq_nonneg (a + 1 / 2), sq_nonneg (a), sq_nonneg (a - 1)]
    have h3_2 : 0 < b ^ 2 + b + 1 := by
      nlinarith [sq_nonneg (b + 1 / 2), sq_nonneg (b), sq_nonneg (b - 1)]
    have h3_3 : 0 < c ^ 2 + c + 1 := by
      nlinarith [sq_nonneg (c + 1 / 2), sq_nonneg (c), sq_nonneg (c - 1)]
    have h3_4 : 1 / (a ^ 2 + a + 1) + 1 / (b ^ 2 + b + 1) + 1 / (c ^ 2 + c + 1) - 1 =
        ((b ^ 2 + b + 1) * (c ^ 2 + c + 1) + (a ^ 2 + a + 1) * (c ^ 2 + c + 1) + (a ^ 2 + a + 1) * (b ^ 2 + b + 1) - (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1)) / ((a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1)) := by
      field_simp
      ring 
    have h3_5 : 0 < (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1) := by
      positivity
    have h3_6 : (b ^ 2 + b + 1) * (c ^ 2 + c + 1) + (a ^ 2 + a + 1) * (c ^ 2 + c + 1) + (a ^ 2 + a + 1) * (b ^ 2 + b + 1) - (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                  sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
                  sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
                  habc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    have h3_7 : ((b ^ 2 + b + 1) * (c ^ 2 + c + 1) + (a ^ 2 + a + 1) * (c ^ 2 + c + 1) + (a ^ 2 + a + 1) * (b ^ 2 + b + 1) - (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1)) / ((a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1)) ≥ 0 := by 
      apply div_nonneg
      linarith [h3_6]
      positivity
    linarith [h3_4, h3_7]
  linarith