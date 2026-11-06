import Mathlib

/- What is the minimum value of $5x^2-20x+1357$? -/
theorem algebra_14117 : IsLeast {y : ℝ | ∃ x, y = 5 * x ^ 2 - 20 * x + 1357} 1337 := by
  constructor
  use 2
  norm_num
  rintro y ⟨x, rfl⟩
  linarith [sq_nonneg (x - 2)]