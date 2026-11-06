import Mathlib

/- For what values of $x$ is it true that $x^2 - 5x - 4 \le 10$? Express your answer in interval notation. -/
theorem algebra_18648 : {x : ℝ | x^2 - 5 * x - 4 ≤ 10} = Set.Icc (-2) 7 := by 
  ext x
  simp
  constructor
  intro h
  constructor <;> nlinarith
  rintro ⟨h₁, h₂⟩
  nlinarith