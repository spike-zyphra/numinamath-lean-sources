import Mathlib

open Finset

theorem number_theory_63200 : (∏ i ∈ range 999, (10^(i + 1) - 1)) % 1000 = 109 := by
  native_decide