import Mathlib

theorem inequalities_200116 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 ≤ a / b + b / c + c / a := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : a / b + b / c + c / a - 3 ≥ 0 := by
    have h3 : a / b + b / c + c / a - 3 = ( (a ^ 2 * c + b ^ 2 * a + b * c ^ 2 ) - 3 * a * b * c ) / (a * b * c ) := by
      field_simp
      ring
    have h4 : (a ^ 2 * c + b ^ 2 * a + b * c ^ 2 ) ≥ 3 * a * b * c := by
      nlinarith [ sq_nonneg (a * c - b * a), sq_nonneg (b * a - c * b ), sq_nonneg (c * b - a * c ), 
          sq_nonneg (a - b ), sq_nonneg (b - c ), sq_nonneg (c - a ), 
          sq_nonneg (a * (a - b )), sq_nonneg (a * (a - c )), 
          sq_nonneg (b * (b - a )), sq_nonneg (b * (b - c )), 
          sq_nonneg (c * (c - a )), sq_nonneg (c * (c - b )), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc 
      ]
    have h5 : ( (a ^ 2 * c + b ^ 2 * a + b * c ^ 2 ) - 3 * a * b * c ) ≥ 0 := by 
      linarith [ h4 ]
    have h6 : ( (a ^ 2 * c + b ^ 2 * a + b * c ^ 2 ) - 3 * a * b * c ) / (a * b * c ) ≥ 0 := by
      apply div_nonneg 
      linarith 
      positivity
    rw [h3]
    linarith
  linarith