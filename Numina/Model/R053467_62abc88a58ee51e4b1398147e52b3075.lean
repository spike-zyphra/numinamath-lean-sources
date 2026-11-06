import Mathlib

theorem algebra_221704 {x y z : ℝ} (h₀ : x + y + z = 50) (h₁ : x - y - z = 8) (h₂ : y - x - z = 8)
    (h₃ : z - x - y = 8) :
    x = 13 ∧ y = 7 ∧ z = 4 := by
  constructor
  · linarith
  constructor
  · linarith
  · linarith