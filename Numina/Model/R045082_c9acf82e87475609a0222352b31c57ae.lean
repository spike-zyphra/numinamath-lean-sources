import Mathlib

theorem inequalities_602768 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / b + b / c + c / a ≥ (a + b) / (b + c) + (b + c) / (a + b) + 1 := by 
  have h1 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  have h2 : 0 < b * c := mul_pos hb hc
  have h3 : 0 < a * b := mul_pos ha hb
  have h4 : 0 < b * c := mul_pos hb hc
  have h5 : 0 < a * c := mul_pos ha hc
  have h6 : 0 < b * a := mul_pos hb ha
  have h7 : 0 < (b + c) * (a + b) := by positivity

  have h8 : 0 < a := ha
  have h9 : 0 < b := hb
  have h10 : 0 < c := hc

  have h11 : 0 < b + c := by linarith
  have h12 : 0 < a + b := by linarith

  have h13 : a / b + b / c + c / a - ((a + b) / (b + c) + (b + c) / (a + b) + 1) ≥ 0 := by
    have pos1 : 0 < b := hb
    have pos2 : 0 < c := hc
    have pos3 : 0 < a := ha
    have pos4 : 0 < b + c := by linarith
    have pos5 : 0 < a + b := by linarith

    have h14 : a / b + b / c + c / a - ((a + b) / (b + c) + (b + c) / (a + b) + 1) =
      ( (a^2 * c * (b + c) * (a + b) ) + (b^2 * a * (b + c) * (a + b)) + (c^2 * b * (b + c) * (a + b)) - ( (a + b) * (a * b * c * (a + b)) ) - ( (b + c) * (a * b * c * (b + c)) ) - ( a * b * c * (b + c) * (a + b) ) ) / ( (a * b * c * (b + c) * (a + b) ) ) := by
      field_simp
      ring
    rw [h14] at *
    apply div_nonneg
    · -- Show that the numerator is non-negative
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        mul_pos (show b + c > 0 by linarith) (show a + b > 0 by linarith), 
        mul_pos (show b + c > 0 by linarith) ha, 
        mul_pos (show b + c > 0 by linarith) hb, 
        mul_pos (show a + b > 0 by linarith) ha, 
        mul_pos (show a + b > 0 by linarith) hb, 
        mul_pos ha (show b * c > 0 by positivity), 
        mul_pos hb (show a * c > 0 by positivity)
      ]
    · -- Show that the denominator is positive
      positivity
  linarith