import Mathlib

theorem algebra_194226 {x : ℝ} (hx : x ≠ 0) (h : 1 - 4/x + 4/x^2 = 0) (A : ℝ) (hA : A = 2/x) :
    A = 1 := by
  have eq1 : 1 - 4 / x + 4 / x ^ 2 = (1 - 2 / x) ^ 2 := by
    field_simp [hx]
    ring
  have eq2 : (1 - 2 / x) ^ 2 = 0 := by 
    rw [eq1] at h 
    linarith 
  have eq3 : 1 - 2 / x = 0 := by 
    apply pow_eq_zero 
    exact eq2 
  have eq4 : 2 / x = 1 := by 
    linarith 
  rw [hA] 
  linarith [eq4]