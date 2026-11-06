import Mathlib

theorem inequalities_85551 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a / b + b / c + c / a ≥ a + b + c := by 
  have h2 : a / b + b / c + c / a - (a + b + c) ≥ 0 := by 
    have h3 : a / b + b / c + c / a - (a + b + c) = (a ^ 2 * c + a * b ^ 2 + b * c ^ 2 - (a + b + c) * (a * b * c)) / (a * b * c) := by
      field_simp
      ring
    have h4 : a ^ 2 * c + a * b ^ 2 + b * c ^ 2 ≥ a + b + c := by
      nlinarith [sq_nonneg (a * a * c - 1), sq_nonneg (b * b * a - 1), sq_nonneg (c * c * b - 1),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc 
        ]
    have h5 : a ^ 2 * c + a * b ^ 2 + b * c ^ 2 - (a + b + c) * (a * b * c) ≥ 0 := by
      have h6 : a ^ 2 * c + a * b ^ 2 + b * c ^ 2 ≥ a + b + c := h4
      have h7 : (a + b + c) * (a * b * c) = (a + b + c) := by 
        calc
          (a + b + c) * (a * b * c) = (a + b + c) * (1) := by
            rw [habc]
          _ = (a + b + c) := by 
            ring
      nlinarith [h7]
    have h8 : (a ^ 2 * c + a * b ^ 2 + b * c ^ 2 - (a + b + c) * (a * b * c)) / (a * b * c) ≥ 0 := by 
      apply div_nonneg 
      linarith 
      positivity
    linarith [h3, h8]
  linarith [h2]