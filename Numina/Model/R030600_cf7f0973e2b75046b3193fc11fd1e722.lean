import Mathlib

open Real Set
open scoped Real

theorem algebra_308886 {α : ℝ} (h₁ : sqrt (1 + sin (2 * α)) = 4 / 3) (h₂ : abs (sin α + cos α) = 4 / 3) :
    (sqrt (1 + sin (2 * α)) = 4 / 3) ↔ (abs (sin α + cos α) = 4 / 3) := by 
  constructor
  · -- Assume sqrt (1 + sin (2 * α)) = 4 / 3, prove abs (sin α + cos α) = 4 / 3
    intro h 
    linarith
  · -- Assume abs (sin α + cos α) = 4 / 3, prove sqrt (1 + sin (2 * α)) = 4 / 3
    intro h
    linarith