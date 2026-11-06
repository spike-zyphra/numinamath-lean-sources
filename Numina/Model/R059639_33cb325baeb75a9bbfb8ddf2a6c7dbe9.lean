import Mathlib

open Finset

theorem number_theory_117313 :
    (∑ i ∈ range 2016, (10^(i + 1) - 1)) + 2016 ≡ 10 [ZMOD 11111] := by 
  native_decide