import Mathlib

theorem number_theory_3283 : (∑ i in Finset.Icc 1998 2017, i^3) - (∑ i in Finset.Icc 989 1008, i^3) ≡ 0 [ZMOD 1009] := by
  native_decide