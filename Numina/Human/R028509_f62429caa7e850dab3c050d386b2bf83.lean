import Mathlib

/- What is the least common multiple of all positive integers smaller than 8? -/
theorem algebra_21547 : Finset.lcm {1, 2, 3, 4, 5, 6, 7} id = 420 := by
  exact rfl