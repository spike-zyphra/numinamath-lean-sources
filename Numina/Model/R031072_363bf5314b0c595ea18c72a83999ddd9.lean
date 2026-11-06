import Mathlib

theorem algebra_17062 {x y : ℝ} (h : x + y = 165000) (h' : x = 4.5 * y) :
    x = 135000 := by
  have eq1 : x + y = 165000 := h
  have eq2 : x = 4.5 * y := h'
  have eq3 : 4.5 * y + y = 165000 := by
    linarith [eq1, eq2]
  have eq4 : y = 30000 := by
    norm_num at eq3
    linarith
  have eq5 : x = 135000 := by
    rw [eq4] at eq2
    norm_num at eq2
    linarith
  exact eq5