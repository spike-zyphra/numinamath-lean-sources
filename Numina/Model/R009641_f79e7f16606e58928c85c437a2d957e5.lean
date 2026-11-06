import Mathlib

open List

def sol_4094 := (Ico 100 1000).filter
  fun n => 20 ∣ n ∧ ¬(55 ∣ n)

theorem prealgebra_4094 : sol_4094.length = 41 := by 
  native_decide