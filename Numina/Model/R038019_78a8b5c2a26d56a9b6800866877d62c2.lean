import Mathlib

theorem algebra_4779 {x y : ℝ} (hy : 2*y-1≠0) (hy' : 1-2*y≠0) (h1 : 2*x+3/(2*y-1)=7) (h2 : x+6/(1-2*y)=1) : x*y=6 := by
  have eq1 : 2 * x * (2 * y - 1) + 3 = 7 * (2 * y - 1) := by 
    have h1' : 2 * y - 1 ≠ 0 := hy
    have eq1 : 2 * x + 3 / (2 * y - 1) = 7 := h1
    field_simp [h1'] at eq1 ⊢
    linarith
  have eq2 : x * (1 - 2 * y) + 6 = 1 - 2 * y := by 
    have h2' : 1 - 2 * y ≠ 0 := hy'
    have eq2 : x + 6 / (1 - 2 * y) = 1 := h2
    field_simp [h2'] at eq2 ⊢
    linarith
  have eq3 : 4 * x * y - 2 * x - 14 * y + 10 = 0 := by 
    linarith [eq1]
  have eq4 : x - 2 * x * y + 2 * y + 5 = 0 := by 
    linarith [eq2]
  have eq5 : 2 * x - 4 * x * y + 4 * y + 10 = 0 := by
    nlinarith [eq4]
  have eq6 : -10 * y + 20 = 0 := by 
    nlinarith [eq3, eq5]
  have hy2 : y = 2 := by 
    linarith [eq6]
  have eq7 : x = 3 := by 
    rw [hy2] at eq4 
    nlinarith 
  have hxy : x * y = 6 := by 
    rw [eq7, hy2] 
    all_goals norm_num
  linarith