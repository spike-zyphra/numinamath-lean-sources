import Mathlib

/- Show that when the product of three conscutive numbers we add arithmetic mean of them it is a perfect cube. -/
theorem algebra_90744 (n : ℤ) :
    ∃ m, m^3 = n * (n + 1) * (n + 2) + (n + (n + 1) + (n + 2)) / 3 := by 
  use n + 1
  -- Simplify the expression for clarity
  ring_nf
  -- Ensure the arithmetic mean is never wrong due to algebraic transformations
  omega