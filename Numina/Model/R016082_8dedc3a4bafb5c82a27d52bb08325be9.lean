import Mathlib


theorem number_theory_213581 : ∃ n, (Nat.digits 10 n).length = 100 ∧
    (Nat.digits 10 n).all (fun d => d ≠ 0) ∧ n % ((Nat.digits 10 n).sum : ℤ) = 0 := by
  use (10^94 - 1) / 9 * 10^6 + 995125
  native_decide