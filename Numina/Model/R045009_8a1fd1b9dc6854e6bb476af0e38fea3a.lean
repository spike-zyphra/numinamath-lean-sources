import Mathlib

open Finset Function

theorem number_theory_609689 :
  #{n ∈ Icc 1 1000000 | n % 1000 > n % 1001} = 499500 := by
  have h2 : #{n ∈ Icc 1 1000000 | n % 1000 > n % 1001} = 499500 := by
    native_decide
  exact h2