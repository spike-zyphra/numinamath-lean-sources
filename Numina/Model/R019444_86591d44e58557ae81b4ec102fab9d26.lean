import Mathlib

theorem inequalities_601623 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a < 1) (h2 : b < 1) :
    a / (1 - b ^ 2) + b / (1 - a ^ 2) ≥ (a + b) / (1 - a * b) := by
  have hb2 : 1 - b^2 > 0 := by
    nlinarith
  have ha2 : 1 - a^2 > 0 := by
    nlinarith
  have hab : 1 - a * b > 0 := by
    nlinarith
  have h4 :  ( a / (1 - b ^ 2) + b / (1 - a ^ 2) ) - ( a + b ) / (1 - a * b ) ≥ 0 := by
    have h5 : (a / (1 - b ^ 2) + b / (1 - a ^ 2) ) - ( a + b ) / (1 - a * b ) = ( a * (1 - a ^ 2) * (1 - a * b) + b * (1 - b ^ 2) * (1 - a * b ) - ( a + b ) * (1 - b ^ 2 ) * (1 - a ^ 2 ) ) / ( (1 - b^2) * (1 - a^2) * (1 - a * b ) ) := by
      field_simp [(show 1 - b ^ 2 ≠ 0 by nlinarith), (show 1 - a ^ 2 ≠ 0 by nlinarith), (show 1 - a * b ≠ 0 by nlinarith)]
      ring
    rw [ h5 ]
    have h6 : ( a * (1 - a^2) * (1 - a * b) + b * (1 - b^2) * (1 - a * b ) - ( a + b ) * (1 - b ^ 2 ) * (1 - a ^ 2 ) ) ≥ 0 := by
      nlinarith [mul_pos ha hb, mul_pos ha (show 0 < 1 - a by linarith), mul_pos hb (show 0 < 1 - b by linarith), sq_nonneg (a - b), sq_nonneg (a * b - a), sq_nonneg (a * b - b), sq_nonneg (a * b), sq_nonneg (a ^ 2 - b ^ 2)]
    have h7' : ( 0 < (1 - b ^ 2 ) * (1 - a ^ 2 ) * (1 - a * b ) ) := by positivity
    apply div_nonneg h6 ( by positivity )
  linarith