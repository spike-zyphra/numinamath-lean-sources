import Mathlib

theorem inequalities_166080 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    2 ≤ a / (c + d) + b / (d + a) + c / (a + b) + d / (b + c) := by
  have h1 : 0 < c + d := by linarith
  have h2 : 0 < d + a := by linarith
  have h3 : 0 < a + b := by linarith
  have h4 : 0 < b + c := by linarith
  have h5 : a / (c + d) + b / (d + a) + c / (a + b) + d / (b + c) - 2 ≥ 0 := by
    have pos1 : 0 < (c + d) * (d + a) * (a + b) * (b + c) := by positivity
    have h6 : a / (c + d) + b / (d + a) + c / (a + b) + d / (b + c) - 2 =
        ( ( a * (d + a) * (a + b) * (b + c) ) + 
          ( b * (c + d) * (a + b) * (b + c) ) + 
          ( c * (c + d) * (d + a) * (b + c) ) + 
          ( d * (c + d) * (d + a) * (a + b) ) - 
          ( 2 * (c + d) * (d + a) * (a + b) * (b + c) ) ) / ( (c + d) * (d + a) * (a + b) * (b + c) ) := by
      field_simp
      <;> ring
    rw [h6] 
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
          sq_nonneg (a + b - c - d), sq_nonneg (a + d - b - c),
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd
        ]
    positivity
  linarith