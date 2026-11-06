import Mathlib

theorem algebra_161494 {P : Polynomial ℝ} (hP : ∀ x, P.eval x = P.eval 0 + P.eval 1 * x + P.eval 2 * x ^ 2)
    (hP' : P.eval (-1) = 1) : P.eval 3 = 5 := by 
  have eq1 := hP (-1)
  rw [hP'] at eq1
  have eq3 := hP 1
  have eq4 := hP 2
  have eq5 := hP 3
  norm_num at eq1 eq3 eq4 
  have h1 : P.eval 0 = -1 := by
    linarith [eq1, eq3, eq4, hP']
  have h2 : P.eval 1 = -1 := by
    linarith [eq1, eq3, eq4, hP']
  have h3 : P.eval 2 = 1 := by
    linarith [eq1, eq3, eq4, hP']
  rw [h1, h2, h3] at eq5
  norm_num at eq5 
  linarith