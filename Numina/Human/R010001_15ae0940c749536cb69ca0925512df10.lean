import Mathlib

/- Find all $x$ such that $x^2+5x<6$. Express your answer in interval notation. -/
theorem algebra_10273 : {x : ℝ | x ^ 2 + 5 * x < 6} = Set.Ioo (-6) 1 := by
  ext x
  simp
  constructor
  intro h
  constructor <;> nlinarith
  rintro ⟨h₁, h₂⟩
  nlinarith
