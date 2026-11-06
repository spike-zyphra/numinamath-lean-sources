import Mathlib

open Finset

theorem number_theory_107518 :
    (∑ i ∈ range 2014, (10^(i + 1) - 1)) + 2014 ≡ 10 [ZMOD 111] := by
  native_decide