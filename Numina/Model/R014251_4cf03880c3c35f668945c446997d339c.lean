import Mathlib

open Real

theorem inequalities_603150 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    2 / (x + y + 2) ≤ 1 / (1 + sqrt x) ^ 2 + 1 / (1 + sqrt y) ^ 2 := by
  have h3 : 0 < sqrt x := Real.sqrt_pos.mpr hx
  have h4 : 0 < sqrt y := Real.sqrt_pos.mpr hy
  have h5 : (1 + sqrt x) ^ 2 > 0 := by positivity
  have h6 : (1 + sqrt y) ^ 2 > 0 := by positivity
  have h7 : (x + y + 2) > 0 := by linarith
  have h8 : 0 < (1 + sqrt x) ^ 2 * (1 + sqrt y) ^ 2 * (x + y + 2) := by positivity
  
  have h9 : 1 / (1 + sqrt x) ^ 2 + 1 / (1 + sqrt y) ^ 2 - 2 / (x + y + 2) ≥ 0 := by
    have h10 : (1 / (1 + sqrt x) ^ 2 + 1 / (1 + sqrt y) ^ 2 - 2 / (x + y + 2)) =
        (( (1 + sqrt x) ^ 2 + (1 + sqrt y) ^ 2 ) * (x + y + 2) - 2 * (1 + sqrt x) ^ 2 * (1 + sqrt y) ^ 2) / (( (1 + sqrt x) ^ 2 * (1 + sqrt y) ^ 2 * (x + y + 2) )) := by
      field_simp [h5, h6, h7]
      <;> ring
      <;> field_simp [h5, h6, h7]
      <;> ring
    rw [h10]

    have h12 : (( (1 + sqrt x) ^ 2 + (1 + sqrt y) ^ 2 ) * (x + y + 2) - 2 * (1 + sqrt x) ^ 2 * (1 + sqrt y) ^ 2 ) ≥ 0 := by
      nlinarith [ sq_nonneg (sqrt x - sqrt y), sq_nonneg (sqrt x - 1), sq_nonneg (sqrt y - 1), 
          sq_nonneg (sqrt x ^ 2 - y), sq_nonneg (sqrt y ^ 2 - x), 
          sq_nonneg (sqrt x * sqrt y - 1), 
          Real.sqrt_pos.mpr hx, Real.sqrt_pos.mpr hy, 
          Real.sq_sqrt (show 0 ≤ x by linarith), Real.sq_sqrt (show 0 ≤ y by linarith),
          mul_nonneg (show 0 ≤ sqrt x by positivity) (show 0 ≤ sqrt y by positivity)
           ]
    
    have h13 : ( (1 + sqrt x) ^ 2 * (1 + sqrt y) ^ 2 * (x + y + 2) ) > 0 := by positivity
    apply div_nonneg
    linarith
    linarith
  
  linarith
  all_goals linarith