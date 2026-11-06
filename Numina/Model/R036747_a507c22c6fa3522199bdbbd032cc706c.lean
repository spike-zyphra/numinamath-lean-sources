import Mathlib

theorem inequalities_268538 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c = 1) :
    a / b + b / c + c / a ≥ a + b + c := by
  have h1 : 0 < a * b * c := by positivity 
  have h2 : a * b * c = 1 := h 

  have h3 : a / b + b / c + c / a - (a + b + c) ≥ 0 := by 
    have h4 : 0 < a * b * c := by positivity
    have eq1 : a / b + b / c + c / a - (a + b + c) = (a ^ 2 * c + b ^ 2 * a + c ^ 2 * b - (a + b + c) * (a * b * c)) / (a * b * c) := by 
      field_simp 
      ring
    rw [eq1] at *
    have h6 : a * b * c > 0 := by positivity 
    -- Prove that the numerator is ≥ 0
    have h5 : a ^ 2 * c + b ^ 2 * a + c ^ 2 * b ≥ (a + b + c) * (a * b * c) := by
      have h7 : a * b * c = 1 := h2 
      have h11 : a * b * c = 1 := h7 
      have h12 : a ^ 2 * c + b ^ 2 * a + c ^ 2 * b ≥ a + b + c := by 
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (a * c - 1), 
          sq_nonneg (a / b - 1), sq_nonneg (b / c - 1), sq_nonneg (c / a - 1), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc 
        ]
      have h13 : (a + b + c) * (a * b * c) = a + b + c := by 
        rw [show (a * b * c) = 1 by linarith [h7] ]
        all_goals nlinarith 
      linarith [h13, h12]
    have h7' : (a ^ 2 * c + b ^ 2 * a + c ^ 2 * b - (a + b + c) * (a * b * c)) ≥ 0 := by 
          nlinarith [h5]
    apply div_nonneg 
    linarith [h7']
    all_goals positivity 
  linarith 
  -- complete positivity.
  all_goals positivity