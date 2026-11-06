import Mathlib

/- What is the value of $x + y + z$ when $6x + 5y - 2z = -4$ and $4x + 5y + 12z = 54$?-/
theorem algebra_21965 (x y z : ℝ) (h₁ : 6 * x + 5 * y - 2 * z = -4) (h₂ : 4 * x + 5 * y + 12 * z = 54) :
    x + y + z = 5 := by
  -- Add the two equations to find $10x+10y+10z=50$.
  have : 10 * x + 10 * y + 10 * z = 50 := by linear_combination h₁ + h₂
  -- Dividing by 10 gives $x+y+z=\boxed{5}$.
  linarith
