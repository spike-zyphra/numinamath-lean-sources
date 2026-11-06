import Mathlib

theorem number_theory_274635 : ∃ n, n^2 ≡ 444 [MOD 1000] := by 
  exact ⟨38, by norm_num [Nat.ModEq]⟩