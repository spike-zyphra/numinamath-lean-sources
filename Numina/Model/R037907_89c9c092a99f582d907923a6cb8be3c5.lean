import Mathlib
open Real

theorem inequalities_95081 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
(a + b) / 2 ≥ sqrt (a * b) := by 
  have h1 : (a + b) ^ 2 / 4 ≥ a * b := by
    nlinarith [sq_nonneg (a - b)]
  have h2 : ( (a + b) / 2 ) ^ 2 ≥ a * b := by 
    linarith [h1]
  have h3 : ( (a + b) / 2 ) ≥ 0 := by 
    nlinarith
  have h4 : sqrt (( (a + b) / 2 ) ^ 2) ≥ sqrt (a * b) := by 
    apply Real.sqrt_le_sqrt
    nlinarith [h2]
  have h5 : sqrt ( ( (a + b ) / 2 ) ^ 2 ) = ( (a + b ) / 2 ) := by 
    rw [Real.sqrt_sq (show ( (a + b ) / 2 ) ≥ 0 by nlinarith ) ]
  have h6 : ( (a + b ) / 2 ) ≥ sqrt (a * b ) := by 
    linarith [ h5, h4 ]
  linarith