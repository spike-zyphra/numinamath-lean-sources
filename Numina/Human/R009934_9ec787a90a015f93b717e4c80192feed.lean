import Mathlib

/- Find the sum of all positive integers such that their expression in base $7$ digits is the reverse of their expression in base $16$ digits. Express your answer in base $10$. -/
theorem number_theory_12305 :
    ∑ n in (Finset.Icc 1 100).filter (fun n => List.reverse (Nat.digits 7 n) = Nat.digits 16 n), n = 58 := by
  native_decide
