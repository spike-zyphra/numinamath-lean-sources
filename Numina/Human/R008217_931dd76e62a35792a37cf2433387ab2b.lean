import Mathlib

/- What is the intersection of the lines given by $2y=-x+3$ and $-y=5x+1$?  Enter the answer as an ordered pair. -/
theorem algebra_15397 (x y : ℝ) (h1 : 2 * y = -x + 3) (h2 : -y = 5 * x + 1) :
    x = -5 / 9 ∧ y = 16 / 9 := by 
  refine' ⟨_, _⟩ <;> linarith