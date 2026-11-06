import Mathlib

theorem algebra_154361 (x : Fin 10 → ℝ) (h : ∀ i, ∑ j in Finset.range 10, (j + 1) * x (i + j) = 55) :
    ∀ i, x i = 1 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 3
  have eq5 := h 4
  have eq6 := h 5
  have eq7 := h 6
  have eq8 := h 7
  have eq9 := h 8
  have eq10 := h 9
  simp [Finset.sum_range_succ] at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10
  have h1 : x 0 = 1 := by 
    norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 
    linarith
  have h2 : x 1 = 1 := by 
    norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 
    linarith
  have h3 : x 2 = 1 := by 
    norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 
    linarith
  have h4 : x 3 = 1 := by 
    norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 
    linarith
  have h5 : x 4 = 1 := by 
    norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 
    linarith
  have h6 : x 5 = 1 := by 
    norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 
    linarith
  have h7 : x 6 = 1 := by 
    norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 
    linarith
  have h8 : x 7 = 1 := by 
    norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 
    linarith
  have h9 : x 8 = 1 := by 
    norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 
    linarith
  have h10 : x 9 = 1 := by 
    norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 
    linarith
  intro i
  fin_cases i <;> simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]