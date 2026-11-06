import Mathlib

/- For what values of $x$ is $x^2-2x>35$? Express your answer in interval notation. -/
theorem algebra_12144 : {x : ℝ | x^2 - 2 * x > 35} = Set.Iio (-5) ∪ Set.Ioi 7 := by
  ext x
  simp
  constructor
  intro hx
  apply or_iff_not_imp_right.2
  intro h
  nlinarith
  rintro (h|h) <;> nlinarith
