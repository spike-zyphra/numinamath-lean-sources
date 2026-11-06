import Mathlib

theorem algebra_215374 {x : ℝ} (hx : x ≠ 0) (h : x + 1 / x = Real.sqrt 2) :
    x ^ 8 + 1 / x ^ 8 = 2 := by 
  have h1 : x * (1 / x) = 1 := by 
    field_simp
  have h2 : x^2 + 1 / x^2 = 0 := by 
    have eq1 : x^2 + 1 / x^2 = (x + 1 / x)^2 - 2 * (x * (1 / x)) := by 
      field_simp
      ring
    rw [eq1, h, h1]
    have h2sq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    linarith [h2sq]
  
  have h3 : x^2 + 1 / x^2 > 0 := by
    have h4 : x^2 > 0 := by
      exact sq_pos_of_ne_zero hx
    have h5 : 1 / x^2 > 0 := by
      positivity
    linarith
  
  linarith [h2, h3]