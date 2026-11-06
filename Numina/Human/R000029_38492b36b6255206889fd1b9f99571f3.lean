import Mathlib

open List

def sol := ((Ico 1 22).product (Ico 1 22)).filter
  fun (a, b) => 1 < a + b ∧ a + b < 22

/- For how many ordered pairs of positive integers \((a, b)\) is \(1 < a + b < 22\)?-/
theorem combinatorics_4056 : sol.length = 210 := by
  -- verify by computation
  native_decide
