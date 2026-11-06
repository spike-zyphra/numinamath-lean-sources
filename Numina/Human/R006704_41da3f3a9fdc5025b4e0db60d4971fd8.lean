import Mathlib

/-Let $K$ be a positive integer. Jack writes whole numbers starting from $1$ and skips all numbers
that contain either the digit 2 or the digit 9. Determine the $K$-th number that Jack writes.
Show that if $K=100$, the $100$-th number Jack writes is 155.-/

theorem number_theory_640330:
  (Finset.filter (fun n => ¬ (n % 10 = 2 ∨ n % 10 = 9 ∨ n / 10 % 10 = 2 ∨ n / 10 % 10 = 9 ∨ n / 100 % 10 = 2 ∨ n / 100 % 10 = 9))
  (Finset.Icc 1 155)).card = 100 := by

  native_decide
