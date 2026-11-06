import Mathlib

theorem algebra_211219 (x : Fin 8 → ℝ)
    (h₀ : x 0 + x 1 + x 2 = 6)
    (h₁ : x 1 + x 2 + x 3 = 9)
    (h₂ : x 2 + x 3 + x 4 = 3)
    (h₃ : x 3 + x 4 + x 5 = -3)
    (h₄ : x 4 + x 5 + x 6 = -9)
    (h₅ : x 5 + x 6 + x 7 = -6)
    (h₆ : x 6 + x 7 + x 0 = -2)
    (h₇ : x 7 + x 0 + x 1 = 2) :
    x = ![1, 2, 3, 4, -4, -3, -2, -1] := by
  have eq1 : x 0 = 1 := by 
    linarith
  have eq2 : x 1 = 2 := by 
    linarith
  have eq3 : x 2 = 3 := by 
    linarith
  have eq4 : x 3 = 4 := by 
    linarith
  have eq5 : x 4 = -4 := by 
    linarith
  have eq6 : x 5 = -3 := by 
    linarith
  have eq7 : x 6 = -2 := by 
    linarith
  have eq8 : x 7 = -1 := by 
    linarith
  funext i 
  fin_cases i 
  all_goals 
    simp [eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8]
    all_goals 
      try { tauto }