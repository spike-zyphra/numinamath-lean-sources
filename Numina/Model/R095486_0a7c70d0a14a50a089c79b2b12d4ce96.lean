import Mathlib

theorem algebra_105248 {x y : ℝ} (hx : x + y = 10) (hy : x - y = 5) :
    x = 7.5 ∧ y = 2.5 := by 
  constructor
  · -- Solving for x by adding the two equations
    have h1 : x = 7.5 := by
      linarith
    exact h1
  · -- Solving for y by substituting x = 7.5 into the first equation
    have h2 : y = 2.5 := by
      linarith
    exact h2