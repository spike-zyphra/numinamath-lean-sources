import Mathlib

/- What is the minimum value of the expression $x^2+y^2+2x-4y+8$ for real $x$ and $y$? -/
theorem algebra_20578 :
  IsLeast {t : ℝ | ∃ x y, t = x ^ 2 + y ^ 2 + 2 * x - 4 * y + 8} 3 := by
  -- rearrange the expression and find perfect square form
  -- x^2+2x = (x+1)^2-1, y^2-4y = (y-2)^2-4
  have h1: ∀x y:ℝ, x^2+y^2+2*x-4*y+8 = (x+1)^2 + (y-2)^2+3 := by
    intro x y; ring
  -- those two square ≥ 0, so whole expression ≥ 3. and equal sign takes when (x+1)^2 = 0 and (y-2)^2=0
  have h2: ∀x y:ℝ, x^2+y^2+2*x-4*y+8 ≥ 3 := by
    intro x y
    rw [h1 x y]
    have hh1 := sq_nonneg (x+1)
    have hh2 := sq_nonneg (y-2)
    linarith [hh1, hh2]
  -- thus we can solve the problem
  rw [IsLeast, lowerBounds]; simp; constructor
  --equal sign takes when (x+1)^2 = 0 and (y-2)^2=0. or x=-1, y=2
  · use (-1); use 2; symm; ring
  · intro a x y ha
    rw [ha]; apply h2 x y