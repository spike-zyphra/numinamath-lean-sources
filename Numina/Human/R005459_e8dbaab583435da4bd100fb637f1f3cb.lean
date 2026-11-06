import Mathlib
/- Find the sum of every even positive integer less than 233 not divisible by 10 . -/
theorem number_theory_608381 : {n ∈ Finset.range 233 | n % 2 = 0 ∧ n % 10 ≠ 0}.sum (fun n => n) = 10812:= by
  decide