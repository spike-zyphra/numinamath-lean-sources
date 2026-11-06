import Mathlib

/- What is the minimum value of the expression $x^2+y^2-6x+4y+18$ for real $x$ and $y$? -/
theorem algebra_11246 : IsLeast {z : ℝ | ∃ x y, z = x^2 + y^2 - 6 * x + 4 * y + 18} 5 := by 
  refine' ⟨⟨3, -2, by norm_num [sq]⟩, _⟩
  rintro z ⟨x, y, rfl⟩
  nlinarith [sq_nonneg (x - 3), sq_nonneg (y + 2)]