import Mathlib

  theorem number_theory_47116 :
  ∃ n : ℕ, 0 < n ∧ 10 ^ 2021 < (3 ^ n) % (2 ^ n) := by
  use 13980
  constructor
  · norm_num
  · native_decide