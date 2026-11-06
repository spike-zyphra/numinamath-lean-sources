import Mathlib

theorem inequalities_100425 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a / (b + c + 1) + b / (a + c + 1) + c / (a + b + 1) ≤ 1) :
    1 / (b + c + 1) + 1 / (a + c + 1) + 1 / (a + b + 1) ≥ 1 := by
  have h1 : b + c + 1 > 0 := by
    linarith
  have h2 : a + c + 1 > 0 := by
    linarith
  have h3 : a + b + 1 > 0 := by
    linarith
  have h4 : a / (b + c + 1) + b / (a + c + 1) + c / (a + b + 1) - 1 ≤ 0 := by
    linarith
  have h6 : (a * (a + c + 1) * (a + b + 1) + b * (b + c + 1) * (a + b + 1) + c * (b + c + 1) * (a + c + 1) ) ≤ ( (b + c + 1) * (a + c + 1) * (a + b + 1) ) := by
    have h'1 : (b + c + 1) * (a + c + 1) * (a + b + 1) ≥ 0 := by
      positivity
    have h'2 : a / (b + c + 1) + b / (a + c + 1) + c / (a + b + 1) - 1 ≤ 0 := by
      linarith
    have h7 : (a / (b + c + 1) + b / (a + c + 1) + c / (a + b + 1) - 1) * ((b + c + 1) * (a + c + 1) * (a + b + 1)) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      linarith
      positivity
    have h8 : (a / (b + c + 1) + b / (a + c + 1) + c / (a + b + 1) - 1) * ((b + c + 1) * (a + c + 1) * (a + b + 1)) = 
        (a * (a + c + 1) * (a + b + 1) + b * (b + c + 1) * (a + b + 1) + c * (b + c + 1) * (a + c + 1) ) - ( (b + c + 1) * (a + c + 1) * (a + b + 1) ) := by
      field_simp [show b + c + 1 > 0 by linarith, show a + c + 1 > 0 by linarith, show a + b + 1 > 0 by linarith]
      ring
    linarith [h8, h7]
  have h8 : 1 / (b + c + 1) + 1 / (a + c + 1) + 1 / (a + b + 1) - 1 ≥ 0 := by
    have h9 : (1 / (b + c + 1) + 1 / (a + c + 1) + 1 / (a + b + 1) - 1 ) = 
        ( (a + c + 1) * (a + b + 1) + (b + c + 1) * (a + b + 1) + (b + c + 1) * (a + c + 1) - (b + c + 1) * (a + c + 1) * (a + b + 1) ) / ( (b + c + 1) * (a + c + 1) * (a + b + 1) ) := by
      field_simp
      ring
    rw [h9]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)
    ]
    positivity
  linarith