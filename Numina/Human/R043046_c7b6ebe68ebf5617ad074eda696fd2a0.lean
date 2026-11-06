import Mathlib

theorem algebra_608354 {x y z : ℝ} : (min x y) + z  = min (x+z)  (y+z) := by 
  by_cases h : x ≤ y 
  have ineq_aux : x + z ≤ y + z := by linarith
  have eq_aux : min x y = x := by 
    simp [h]
  have eq_aux' : min (x + z) (y + z) = x + z := by 
    simp [h]
  rw [eq_aux, eq_aux']
  simp at h
  have eq_aux : min x y = y := by 
    simp 
    linarith
  have eq_aux' : min (x + z) (y + z) = y + z := by 
    simp
    linarith
  rw [eq_aux, eq_aux']
  