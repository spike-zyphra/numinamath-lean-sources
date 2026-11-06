import Mathlib

theorem inequalities_8810 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + 2 * c) / (c + 2 * a) ^ 2 + (b + c + 2 * a) / (a + 2 * b) ^ 2 +
    (c + a + 2 * b) / (b + 2 * c) ^ 2 ≥
    4 / (a + b + c) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : 0 < (c + 2 * a) := by
    linarith 
  have h3 : 0 < (a + 2 * b) := by
    linarith 
  have h4 : 0 < (b + 2 * c) := by
    linarith 
  have h5 : 0 < (c + 2 * a) ^ 2 := by 
    positivity 
  have h6 : 0 < (a + 2 * b) ^ 2 := by
    positivity 
  have h7 : 0 < (b + 2 * c) ^ 2 := by
    positivity 
  have h8 : 0 < a + b + c := by 
    linarith
  have h9 : (a + b + 2 * c) / (c + 2 * a) ^ 2 + (b + c + 2 * a) / (a + 2 * b) ^ 2 + (c + a + 2 * b) / (b + 2 * c) ^ 2 - 4 / (a + b + c) ≥ 0 := by 
    have h10 : 0 < (c + 2 * a) ^ 2 * (a + 2 * b) ^ 2 * (b + 2 * c) ^ 2 * (a + b + c) := by 
      positivity 
    have h11 : ( (a + b + 2 * c) / (c + 2 * a) ^ 2 + (b + c + 2 * a) / (a + 2 * b) ^ 2 + (c + a + 2 * b) / (b + 2 * c) ^ 2 - 4 / (a + b + c) ) = 
      ( (a + b + 2 * c) * (a + 2 * b) ^ 2 * (b + 2 * c) ^ 2 * (a + b + c) + (b + c + 2 * a) * (c + 2 * a) ^ 2 * (b + 2 * c) ^ 2 * (a + b + c) + (c + a + 2 * b) * (c + 2 * a) ^ 2 * (a + 2 * b) ^ 2 * (a + b + c) - 4 * (c + 2 * a) ^ 2 * (a + 2 * b) ^ 2 * (b + 2 * c) ^ 2 ) / ( (c + 2 * a) ^ 2 * (a + 2 * b) ^ 2 * (b + 2 * c) ^ 2 * (a + b + c) ) := by 
      field_simp
      ring 
    rw [h11] 
    apply div_nonneg 
    nlinarith [ sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (b * c - c * a), 
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
      sq_nonneg (a * (a - b) ), sq_nonneg (a * (a - c) ), sq_nonneg (a * (b - c) ), 
      sq_nonneg (b * (a - b) ), sq_nonneg (b * (a - c) ), sq_nonneg (b * (b - c) ), 
      sq_nonneg (c * (a - b) ), sq_nonneg (c * (a - c) ), sq_nonneg (c * (b - c) ), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc 
    ]
    all_goals positivity 
  linarith