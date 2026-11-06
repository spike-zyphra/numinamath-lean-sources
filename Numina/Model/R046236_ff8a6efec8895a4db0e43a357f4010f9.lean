import Mathlib

theorem algebra_240613 {a b c d : ℤ} (h : ¬(a = b ∧ b = c ∧ c = d)) :
    ∃ n, (a - b) * 4 ^ n > 1985 ∨ (b - c) * 4 ^ n > 1985 ∨ (c - d) * 4 ^ n > 1985 ∨
    (d - a) * 4 ^ n > 1985 := by
  use 7
  norm_num
  omega