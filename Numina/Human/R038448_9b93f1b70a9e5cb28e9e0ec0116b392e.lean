import Mathlib

/- Find all $c$ which satisfy $$\frac{c}{3} \le 2+c < -2(1+c).$$Express your answer in interval notation, simplifying any fractions which occur in your answer. -/
theorem algebra_13783 : {c : ℝ | c / 3 ≤ 2 + c ∧ 2 + c < -2 * (1 + c)} = Set.Ico (-3) (-4 / 3) := by
  ext c
  constructor <;> intro h <;> simp_all [Set.Ico]
  <;> constructor <;> linarith
