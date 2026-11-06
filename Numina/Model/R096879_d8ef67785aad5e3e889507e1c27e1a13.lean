import Mathlib

theorem algebra_176130 (x : Fin 3 → ℝ)
    (h1 : x 0 + 2 * x 1 + 4 * x 2 = 5)
    (h2 : 2 * x 0 + x 1 + 5 * x 2 = 7)
    (h3 : 3 * x 0 + 2 * x 1 + 6 * x 2 = 9) :
    x 0 = 1 ∧ x 1 = 0 ∧ x 2 = 1 := by 
  have eq4 : x 1 + x 2 = 1 := by 
    linarith [h1, h2]
  have eq5 : 4 * x 1 + 6 * x 2 = 6 := by 
    linarith [h1, h3]
  have hx2 : x 2 = 1 := by
    linarith [eq4, eq5]
  have hx1 : x 1 = 0 := by 
    linarith [eq4, hx2]
  have hx0 : x 0 = 1 := by 
    linarith [h1, hx1, hx2]
  exact ⟨hx0, hx1, hx2⟩