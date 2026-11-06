import Mathlib

theorem algebra_202963 (x : Fin 5 → ℝ)
    (h1 : x 0 + 2 * x 1 + 2 * x 2 + 2 * x 3 + 2 * x 4 = 1)
    (h2 : x 0 + 3 * x 1 + 4 * x 2 + 4 * x 3 + 4 * x 4 = 2)
    (h3 : x 0 + 3 * x 1 + 5 * x 2 + 6 * x 3 + 6 * x 4 = 3)
    (h4 : x 0 + 3 * x 1 + 5 * x 2 + 7 * x 3 + 8 * x 4 = 4)
    (h5 : x 0 + 3 * x 1 + 5 * x 2 + 7 * x 3 + 9 * x 4 = 5) :
    x = ![1, -1, 1, -1, 1] := by

  have hx4 : x 4 = 1 := by
    linarith 
  have hx3 : x 3 = -1 := by 
    have eq1 : x 3 + 2 * x 4 = 1 := by 
      linarith [h3, h4]
    rw [hx4] at eq1
    linarith 
  have hx2 : x 2 = 1 := by 
    have eq2 : x 2 + 2 * x 3 + 2 * x 4 = 1 := by 
      linarith [h2, h3]
    rw [hx3, hx4] at eq2
    linarith 
  have hx1 : x 1 = -1 := by 
    have eq3 : x 1 + 2 * x 2 + 2 * x 3 + 2 * x 4 = 1 := by 
      linarith [h1, h2]
    rw [hx2, hx3, hx4] at eq3
    linarith 
  have hx0 : x 0 = 1 := by 
    linarith [h1, hx1, hx2, hx3, hx4]
  funext i
  fin_cases i <;> simp [hx0, hx1, hx2, hx3, hx4]
  all_goals linarith