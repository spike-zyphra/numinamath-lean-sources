import Mathlib

theorem number_theory_207110 : ∃ k : ℤ, (1989 * 1991 ^ 1990 - 1990 * 1991 ^ 1989 + 1 : ℝ) / 1990 ^ 2 = k := by
  use ( (1989 * 1991 ^ 1990 - 1990 * 1991 ^ 1989 + 1) / (1990 ^ 2) )
  norm_num