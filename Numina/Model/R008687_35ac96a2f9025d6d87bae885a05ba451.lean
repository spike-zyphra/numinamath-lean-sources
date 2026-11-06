import Mathlib

theorem number_theory_14203 : (Nat.ofDigits 9 [7, 5, 3, 1] / Nat.ofDigits 4 [0, 0, 1] : ℤ) -
    Nat.ofDigits 8 [0, 6, 4, 2] + Nat.ofDigits 9 [8, 7, 6, 5] =
    2938 := by
  norm_num [Nat.ofDigits]