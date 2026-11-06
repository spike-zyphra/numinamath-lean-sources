import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_23371 : (-4, 0) = (4 * cos π, 4 * sin π) := by
  have h1 : -4 = 4 * cos π := by
    rw [cos_pi]
    ring
  have h2 : 0 = 4 * sin π := by
    rw [sin_pi]
    ring
  exact Prod.ext h1 h2