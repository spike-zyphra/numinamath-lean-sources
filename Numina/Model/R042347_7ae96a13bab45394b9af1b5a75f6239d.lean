import Mathlib

theorem inequalities_209559 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 + a + b + c = 2 * a * b * c) :
    3 / 2 ≤ a * b / (1 + a + b) + b * c / (1 + b + c) + c * a / (1 + c + a) := by

  have h1 : 0 < (1 + a + b) := by positivity
  have h2 : 0 < (1 + b + c) := by positivity
  have h3 : 0 < (1 + c + a) := by positivity 
  have h4 : a * b / (1 + a + b) + b * c / (1 + b + c) + c * a / (1 + c + a) - 3 / 2 ≥ 0 := by

    have pos1 : 0 < (1 + a + b) * (1 + b + c) * (1 + c + a) := by positivity

    have h5 : a * b / (1 + a + b) + b * c / (1 + b + c) + c * a / (1 + c + a) - 3 / 2 =
        ( 2 * a * b * (1 + b + c) * (1 + c + a) + 2 * b * c * (1 + a + b) * (1 + c + a) + 2 * c * a * (1 + a + b) * (1 + b + c) - 3 * (1 + a + b) * (1 + b + c) * (1 + c + a) ) / (2 * (1 + a + b) * (1 + b + c) * (1 + c + a)) := by 
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    -- Show that the numerator is non-negative
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        mul_pos (mul_pos ha hb) hc, 
        h
      ]
    -- Show the denominator is non-negative
    positivity
  linarith