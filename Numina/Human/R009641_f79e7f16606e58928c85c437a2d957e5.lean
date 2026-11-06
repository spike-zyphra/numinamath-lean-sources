import Mathlib

open List

def sol_4094 := (Ico 100 1000).filter
  fun n => 20 ∣ n ∧ ¬(55 ∣ n)

/- How many positive $3$-digit numbers are multiples of $20$, but not of $55$?-/
theorem prealgebra_4094 : sol_4094.length = 41 := by
  -- verify by computation
  native_decide
