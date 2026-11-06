import Mathlib

/- Find all $x$ that satisfy the inequality $(2x+10)(x+3)<(3x+9)(x+8)$. Express your answer in interval notation. -/
theorem algebra_20432 : {x : ℝ | (2 * x + 10) * (x + 3) < (3 * x + 9) * (x + 8)} = Set.Iio (-14) ∪ Set.Ioi (-3) := by
  ext x
  simp
  constructor
  intro h
  apply or_iff_not_imp_right.2
  intro hx
  nlinarith
  rintro (h | h) <;> nlinarith
