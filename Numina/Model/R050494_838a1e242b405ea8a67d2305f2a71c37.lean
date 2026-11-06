import Mathlib

theorem number_theory_64346 :
    ∃ k : ℕ, 0 < k ∧ ¬(Nat.digits 10 ((1996 * k) + (1997 * k))).any (fun d => d > 9) := by
  use 222
  constructor
  · norm_num
  · norm_num