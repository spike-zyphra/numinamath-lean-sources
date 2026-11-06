import Mathlib

theorem algebra_603180 (x : Fin 8 → ℝ)
    (h1 : x 0 + x 1 + x 2 = 6)
    (h2 : x 1 + x 2 + x 3 = 9)
    (h3 : x 2 + x 3 + x 4 = 3)
    (h4 : x 3 + x 4 + x 5 = -3)
    (h5 : x 4 + x 5 + x 6 = -9)
    (h6 : x 5 + x 6 + x 7 = -6)
    (h7 : x 6 + x 7 + x 0 = -2)
    (h8 : x 7 + x 0 + x 1 = 2) :
    x 0 = 1 ∧ x 1 = 2 ∧ x 2 = 3 ∧ x 3 = 4 ∧ x 4 = -4 ∧ x 5 = -3 ∧ x 6 = -2 ∧ x 7 = -1 := by
  constructor
  · -- Prove x 0 = 1
    linarith [h1, h2, h3, h4, h5, h6, h7, h8]
  constructor
  · -- Prove x 1 = 2
    linarith [h1, h2, h3, h4, h5, h6, h7, h8]
  constructor
  · -- Prove x 2 = 3
    linarith [h1, h2, h3, h4, h5, h6, h7, h8]
  constructor
  · -- Prove x 3 = 4
    linarith [h1, h2, h3, h4, h5, h6, h7, h8]
  constructor
  · -- Prove x 4 = -4
    linarith [h1, h2, h3, h4, h5, h6, h7, h8]
  constructor
  · -- Prove x 5 = -3
    linarith [h1, h2, h3, h4, h5, h6, h7, h8]
  constructor
  · -- Prove x 6 = -2
    linarith [h1, h2, h3, h4, h5, h6, h7, h8]
  · -- Prove x 7 = -1
    linarith [h1, h2, h3, h4, h5, h6, h7, h8]