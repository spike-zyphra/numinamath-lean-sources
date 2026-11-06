import Mathlib

/- What is the smallest possible real value of $x^2 + 8x$? -/
theorem algebra_13509 : IsLeast {x | ∃ y : ℝ, x = y^2 + 8 * y} (-16) := by
  refine' ⟨⟨-4, by ring⟩, _⟩
  rintro x ⟨y, rfl⟩
  nlinarith [sq_nonneg (y + 4)]