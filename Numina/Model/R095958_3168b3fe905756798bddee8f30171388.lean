import Mathlib

theorem algebra_223105 (x : Fin 5 → ℝ)
    (h1 : x 0 + 2 * x 1 + 2 * x 2 + 2 * x 3 + 2 * x 4 = 1)
    (h2 : x 0 + 3 * x 1 + 4 * x 2 + 4 * x 3 + 4 * x 4 = 2)
    (h3 : x 0 + 3 * x 1 + 5 * x 2 + 6 * x 3 + 6 * x 4 = 3)
    (h4 : x 0 + 3 * x 1 + 5 * x 2 + 7 * x 3 + 8 * x 4 = 4)
    (h5 : x 0 + 3 * x 1 + 5 * x 2 + 7 * x 3 + 9 * x 4 = 5) :
    x 0 = 1 ∧ x 2 = 1 ∧ x 4 = 1 ∧ x 1 = -1 ∧ x 3 = -1 := by
  have h6 : x 4 = 1 := by
    linarith
  have h7 : x 3 = -1 := by
    linarith [h4, h6]
  have h8 : x 2 = 1 := by
    linarith [h3, h6, h7]
  have h9 : x 1 = -1 := by
    linarith [h1, h2, h8, h7, h6]
  have h10 : x 0 = 1 := by 
    linarith [h1, h9, h8, h7, h6]
  exact ⟨h10, h8, h6, h9, h7⟩