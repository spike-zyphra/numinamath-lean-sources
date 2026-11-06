import Mathlib

/- What is the minimum value of the expression $2x^2+3y^2+8x-24y+62$ for real $x$ and $y$? -/
theorem algebra_21342 : IsLeast {n : ℝ | ∃ x y, n = 2*x^2 + 3*y^2 + 8*x - 24*y + 62} 6 := by 
  constructor
  use -2
  use 4
  norm_num
  rintro n ⟨x, y, rfl⟩
  nlinarith [sq_nonneg (x + 2), sq_nonneg (y - 4)]