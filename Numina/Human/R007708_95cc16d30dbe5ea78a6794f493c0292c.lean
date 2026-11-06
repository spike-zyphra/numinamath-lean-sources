import Mathlib

/- For what values of $x$ is $2x^2+8x\le-6$? Express your answer in interval notation. -/
theorem algebra_11236 : {x : ℝ | 2 * x ^ 2 + 8 * x ≤ -6} = Set.Icc (-3) (-1) := by
  ext x
  simp
  constructor
  intro h
  constructor <;> nlinarith
  rintro ⟨h₁, h₂⟩
  nlinarith
