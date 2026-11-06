import Mathlib

theorem algebra_136656 {x : Fin 3 → ℝ}
    (h1 : 3 * x 0 - 2 * x 1 + x 2 = -10)
    (h2 : 2 * x 0 + 3 * x 1 - 4 * x 2 = 16)
    (h3 : x 0 - 4 * x 1 + 3 * x 2 = -18) :
    x 0 = -1 ∧ x 1 = 2 ∧ x 2 = -3 := by 
  constructor
  · linarith 
  constructor
  · linarith 
  · linarith