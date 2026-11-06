import Mathlib

/- Find all solutions $x$ of the inequality $$\frac{5}{24} + \left|x-\frac{11}{48}\right| < \frac{5}{16}.$$Express your answer in interval notation, simplifying all fractions in your answer. -/
theorem algebra_15630 : {x : ℝ | 5 / 24 + abs (x - 11 / 48) < 5 / 16} = Set.Ioo (1 / 8) (1 / 3) := by
  ext x
  simp only [Set.mem_Ioo, Set.mem_setOf_eq]
  constructor
  intro h
  have key := abs_lt.mp (show |x - 11 / 48| < 5 / 48 by linarith)
  constructor <;> linarith
  rintro ⟨h₀, h₁⟩
  have key : |x - 11 / 48| < 5 / 48 := by
    rw [abs_lt]
    constructor <;> linarith
  linarith
