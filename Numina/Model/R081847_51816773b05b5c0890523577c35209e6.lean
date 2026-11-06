import Mathlib

theorem algebra_12071 (a b c : ℝ) (ha : a ≠ 0) (h1 : a * (-1)^2 + b * (-1) + c = 7)
    (h2 : a * 5^2 + b * 5 + c = 7) (h3 : a * 6^2 + b * 6 + c = 10) :
    -b / (2 * a) = 2 := by

  have eq1 : a - b + c = 7 := by linarith 
  have eq2 : 25 * a + 5 * b + c = 7 := by linarith 
  have eq3 : 36 * a + 6 * b + c = 10 := by linarith

  have eq4 : 4 * a + b = 0 := by 
    linarith [eq1, eq2]

  have eq5 : 11 * a + b = 3 := by 
    linarith [eq2, eq3]

  have ha_val : a = 3 / 7 := by 
    have h1 : 7 * a = 3 := by linarith [eq4, eq5]
    linarith

  have hb_val : b = -12 / 7 := by 
    rw [ha_val] at eq4
    linarith

  have hx_vertex : -b / (2 * a) = 2 := by 
    rw [hb_val, ha_val]
    field_simp
    norm_num

  exact hx_vertex