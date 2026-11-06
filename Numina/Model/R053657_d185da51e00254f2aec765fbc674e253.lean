import Mathlib

def S : ℕ → ℕ
| n => (Nat.digits 10 n).sum

theorem number_theory_39626 :
    ∃ n, n + S n = 1980 := by
  use 1962
  norm_num [S]