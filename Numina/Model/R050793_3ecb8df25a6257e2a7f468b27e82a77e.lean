import Mathlib

theorem inequalities_265857 (a b c : ℝ) (ha : a > b) (hb : b > c) :
    1 / (a - b) + 1 / (b - c) ≥ 4 / (a - c) := by
  have h1 : a - b > 0 := by linarith 
  have h2 : b - c > 0 := by linarith 
  have h3 : a - c > 0 := by linarith 
  have h6 : 0 < (a - b) * (b - c) * (a - c) := by 
    positivity 
  have h5 : (1 / (a - b) + 1 / (b - c) - 4 / (a - c)) ≥ 0 := by 
    have h5 : (1 / (a - b) + 1 / (b - c) - 4 / (a - c)) = 
      (( (b - c) * (a - c) + (a - b) * (a - c) - 4 * (a - b) * (b - c) ) / ( (a - b) * (b - c) * (a - c) )) := by
        field_simp 
        ring 
    rw [h5] 
    apply div_nonneg 
    nlinarith [sq_nonneg (a - c), sq_nonneg ((a - b) - (b - c)), sq_nonneg (2 * (a - b) - (a - c)), sq_nonneg ((b - c) - (a - c)), mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb) ]
    positivity 
  linarith