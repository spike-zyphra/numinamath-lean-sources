import Mathlib

open Real
open scoped BigOperators
theorem inequalities_79152 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  (a ^ 2 + b ^ 2) * (a + c) / b + (b ^ 2 + c ^ 2) * (b + a) / c +
  (c ^ 2 + a ^ 2) * (c + b) / a ≥ 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < c := hc
  have h4 : 0 < a * b * c := by
    positivity

  have h5 : (a ^ 2 + b ^ 2) * (a + c) / b + (b ^ 2 + c ^ 2) * (b + a) / c + (c ^ 2 + a ^ 2) * (c + b) / a - 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 0 := by
    have pos1 : 0 < a * b * c := by positivity
    have h6 : (a ^ 2 + b ^ 2) * (a + c) / b + (b ^ 2 + c ^ 2) * (b + a) / c + (c ^ 2 + a ^ 2) * (c + b) / a - 2 * (a ^ 2 + b ^ 2 + c ^ 2) =
        ( (a^2 + b^2) * (a + c) * a * c + (b^2 + c^2) * (b + a) * a * b + (c^2 + a^2) * (c + b) * b * c - 2 * (a^2 + b^2 + c^2) * (a * b * c) ) / (a * b * c) := by
      field_simp
      ring
    rw [h6]
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < a^2 by positivity) (show 0 < b^2 by positivity), 
          mul_pos (show 0 < b^2 by positivity) (show 0 < c^2 by positivity), 
          mul_pos (show 0 < a^2 by positivity) (show 0 < c^2 by positivity)]
    
    positivity
  
  linarith