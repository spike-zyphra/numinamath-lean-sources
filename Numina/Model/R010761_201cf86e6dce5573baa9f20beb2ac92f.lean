import Mathlib

theorem number_theory_23123 : ∃ n, 0 ≤ n ∧ n < 2293 ∧ 31 * n ≡ 3 [ZMOD 2293] := by
  use 222
  constructor
  · norm_num
  constructor
  · norm_num
  · -- 31 * 222 ≡ 3 [ZMOD 2293]
    norm_num [Int.ModEq]
    <;> omega