import Mathlib

theorem number_theory_274635 : ∃ n, n^2 ≡ 444 [MOD 1000] := by 
  use 38
  norm_num [Nat.ModEq]