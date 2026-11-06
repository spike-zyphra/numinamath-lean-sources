import Mathlib

open Real

theorem algebra_97899 (x : ℝ) (hx : 0 < x ∧ x ≠ 1) :
    logb 3 x * logb x 5 = logb 3 5 := by
  have hx1 : 0 < x := hx.1
  have hx2 : x ≠ 1 := hx.2

  have h1 : logb 3 x = (log x) / (log (3 : ℝ)) := by
    field_simp [logb]
  
  have h2 : logb x 5 = (log (5 : ℝ)) / (log x) := by 
    field_simp [logb]
  
  have h3 : logb 3 5 = (log (5 : ℝ)) / (log (3 : ℝ)) := by 
    field_simp [logb]

  rw [h1, h2, h3]

  have h4 : x > 0 := hx1
  have h5 : log x ≠ 0 := by
    have hx2' : x ≠ 1 := hx2
    exact log_ne_zero_of_pos_of_ne_one (show (0 : ℝ) < x by linarith) hx2'
  
  field_simp [h5]
  <;> ring