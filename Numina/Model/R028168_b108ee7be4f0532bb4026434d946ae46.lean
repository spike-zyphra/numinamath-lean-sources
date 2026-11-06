import Mathlib

theorem algebra_223113 (x : Fin 8 → ℝ)
    (h₀ : x 0 + x 1 + x 2 = 6)
    (h₁ : x 1 + x 2 + x 3 = 9)
    (h₂ : x 2 + x 3 + x 4 = 3)
    (h₃ : x 3 + x 4 + x 5 = -3)
    (h₄ : x 4 + x 5 + x 6 = -9)
    (h₅ : x 5 + x 6 + x 7 = -6)
    (h₆ : x 6 + x 7 + x 0 = -2)
    (h₇ : x 7 + x 0 + x 1 = 2) :
    x 0 = -x 7 ∧ x 0 = 1 ∧ x 1 = -x 6 ∧ x 1 = 2 ∧
    x 2 = -x 5 ∧ x 2 = 3 ∧ x 3 = -x 4 ∧ x 3 = 4 := by
  constructor
  · -- Prove that x 0 = -x 7
    linarith
  constructor
  · -- Prove that x 0 = 1
    linarith
  constructor
  · -- Prove that x 1 = -x 6
    linarith
  constructor
  · -- Prove that x 1 = 2
    linarith
  constructor
  · -- Prove that x 2 = -x 5
    linarith
  constructor
  · -- Prove that x 2 = 3
    linarith
  constructor
  · -- Prove that x 3 = -x 4
    linarith
  · -- Prove that x 3 = 4
    linarith