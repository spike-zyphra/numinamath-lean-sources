import Mathlib

theorem number_theory_125083 {a b : GaussianInt} :
    (a * b).norm = a.norm * b.norm := by
  simp [pow_two, Complex.normSq, Complex.ext_iff, mul_add, add_mul]
  all_goals
    ring