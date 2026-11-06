import Mathlib

theorem inequalities_55761 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 3 * a * b * c) :
    9 / (a + b + c) ≤ a / (b^2 * c^2) + b / (c^2 * a^2) + c / (a^2 * b^2) := by
  have h1 : 0 < a * b * c := by
    positivity
  have h1' : 0 < a + b + c := by 
    linarith 
  have h2 : a / (b^2 * c^2) + b / (c^2 * a^2) + c / (a^2 * b^2) - 9 / (a + b + c) ≥ 0 := by 
    have h3 : a / (b^2 * c^2) + b / (c^2 * a^2) + c / (a^2 * b^2) - 9 / (a + b + c) = ( 
        (a^3 + b^3 + c^3) * (a + b + c) - 9 * (a * b * c) ^ 2 
      ) / ( (a^2 * b^2 * c^2) * (a + b + c) ) := by 
      field_simp
      ring
    rw [h3] at *
    have h4 : ( (a^3 + b^3 + c^3) * (a + b + c) - 9 * (a * b * c) ^ 2 ) ≥ 0 := by
      nlinarith [ sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
        sq_nonneg (a * (a - b) ), sq_nonneg (a * (a - c) ), 
        sq_nonneg (b * (b - c) ), sq_nonneg (b * (b - a) ), 
        sq_nonneg (c * (c - a) ), sq_nonneg (c * (c - b) ), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        mul_pos (show 0 < a * b by positivity) (show 0 < a * b * c by positivity), 
        mul_pos (show 0 < a * b by positivity) (show 0 < c by positivity), 
        mul_pos (show 0 < a * c by positivity) (show 0 < b * c by positivity) 
      ]
    have h5 : ( (a^2 * b^2 * c^2) * (a + b + c) ) > 0 := by 
      positivity 
    apply div_nonneg 
    linarith
    all_goals
      positivity
  linarith [ h2 ]