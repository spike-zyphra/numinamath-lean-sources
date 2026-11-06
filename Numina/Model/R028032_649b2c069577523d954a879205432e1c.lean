import Mathlib

theorem number_theory_239512 : ∃ n m, n * m = 1000000 ∧ ∀ d ∈ Nat.digits 10 n, d ≠ 0 ∧
    ∀ d ∈ Nat.digits 10 m, d ≠ 0 := by
  use 15625, 64
  constructor
  · norm_num
  · intro d hd
    norm_num [Nat.digits, Nat.digitsAux] at hd ⊢
    all_goals omega