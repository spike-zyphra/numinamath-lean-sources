import Mathlib

theorem number_theory_171669 :
    ∃ a b c d : ℤ, |a| > 1000000 ∧ |b| > 1000000 ∧ |c| > 1000000 ∧ |d| > 1000000 ∧
      1 / a + 1 / b + 1 / c + 1 / d = 1 / (a * b * c * d) := by
  use 2 * 1000001
  use -3 * 1000001
  use -4 * 1000001
  use 12 * 1000001
  norm_num [abs]