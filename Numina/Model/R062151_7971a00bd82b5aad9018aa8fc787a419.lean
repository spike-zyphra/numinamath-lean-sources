import Mathlib

theorem algebra_603127 (x y z u v : ℝ)
    (h₀ : x - y + z = 1) (h₁ : y - z + u = 2) (h₂ : z - u + v = 3)
    (h₃ : u - v + x = 4) (h₄ : v - x + y = 5) :
    x = 0 ∧ y = 6 ∧ z = 7 ∧ u = 3 ∧ v = -1 := by 
  constructor
  · -- Solving x = 0
    linarith
  constructor
  · -- Solving y = 6
    linarith
  constructor
  · -- Solving z = 7
    linarith
  constructor
  · -- Solving u = 3
    linarith
  · -- Solving v = -1
    linarith