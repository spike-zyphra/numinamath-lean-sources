import Mathlib

theorem number_theory_23366 : ∃ n : ℕ, 0 ≤ n ∧ n < 398 ∧ n * 7 ≡ 1 [MOD 398] := by
  use 57
  constructor
  · norm_num
  constructor
  · norm_num
  · 
    norm_num [Nat.ModEq]