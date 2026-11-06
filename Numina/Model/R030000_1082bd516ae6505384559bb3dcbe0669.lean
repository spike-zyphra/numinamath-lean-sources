import Mathlib

open Nat Finset

def P (n : ℤ) : ℤ := (n - 2) * n * (n - 1) * (n - 7)

#eval primeFactorsList 1001  

theorem numbertheory_609719 :
    ∑ n in Icc 1 2017, (if (1001 ∣ P n) then (1 : ℕ) else 0) = 99 := by

  native_decide