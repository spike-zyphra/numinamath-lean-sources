import Mathlib

theorem algebra_177287 (d : ℝ) (h : d = 6) (v s : ℝ)
    (h1 : v > 0) (h2 : s > 0) (h3 : d / 2 / v + d / 2 / s = d / 10 / v + d / 10 / s)
    (h4 : d / 2 / s = d / 5 / v) :
    v = 15 := by 

  rw [h] at h4 h3
  have eq1 : 5 * v = 2 * s := by 
    field_simp at h4 
    nlinarith
  
  have eq2 : 15 * s + 15 * v = 3 * s + 3 * v := by 
    field_simp at h3
    nlinarith [h1, h2, sq_pos_of_pos h1, sq_pos_of_pos h2]

  have eq3 : s + v = 0 := by
    nlinarith
  
  have eq4 : s + v > 0 := by
    linarith
  
  linarith