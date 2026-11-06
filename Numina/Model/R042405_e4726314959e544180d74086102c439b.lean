import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_23371 : (-4, 0) = (4 * cos π, 4 * sin π) := by 
  have h1 : cos π = -1 := by 
    exact cos_pi
  have h2 : sin π = 0 := by 
    exact sin_pi
  simp [h1, h2]