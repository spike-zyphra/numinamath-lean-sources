import Mathlib

open List

def sol_4090 := ((Ico 100 126).append (Ico 200 226)).map
  fun n => (if n % 10 = 1 then 1 else 0) +
    (if n % 100 / 10 = 1 then 1 else 0) +
    (if n % 1000 / 100 = 1 then 1 else 0)

theorem prealgebra_4090 : sol_4090.sum = 52 := by 
  simp [sol_4090, Ico, Nat.lt_succ_iff]
  <;> native_decide