import Mathlib

theorem number_theory_15992 : ∃ n, 0 ≤ n ∧ n < 9 ∧ (-1111 : ℤ) ≡ n [ZMOD 9] := by
  use 5
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num [Int.ModEq]