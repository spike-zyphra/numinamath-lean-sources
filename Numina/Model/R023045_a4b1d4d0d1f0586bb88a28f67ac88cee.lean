import Mathlib

theorem algebra_198168 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x * 1.04 = y * 0.91) (h' : y / x = 5.6 / 100) :
    y / x = 4.9 / 100 := by

  have eq1 : y = x * (5.6 / 100) := by 
    have eq2 : y / x = (5.6 / 100 : ℝ) := by 
      simpa using h'
    have eq3 : y = x * (y / x) := by 
      field_simp [hx]
    rw [eq2] at eq3 
    linarith

  have eq2 : x * (1.04 : ℝ) = (x * (5.6 / 100 : ℝ)) * (0.91 : ℝ) := by 
    rw [eq1] at h 
    linarith
  
  have eq3 : x * (1.04 - (5.6 / 100 * 0.91)) = 0 := by
    have eq4 : x * (1.04 : ℝ) = (x * (5.6 / 100 : ℝ)) * (0.91 : ℝ) := eq2
    linarith [eq4]

  have eq4 : (1.04 - (5.6 / 100 * 0.91) : ℝ) = 0 := by 
    apply (mul_left_inj' hx).mp 
    linarith [eq3]

  have h1 : (1.04 - (5.6 / 100 * 0.91) : ℝ) ≠ 0 := by 
    norm_num
  
  contradiction