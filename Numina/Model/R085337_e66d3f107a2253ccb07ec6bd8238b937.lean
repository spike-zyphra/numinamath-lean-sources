import Mathlib

theorem number_theory_218502 : ∑ i in Finset.Icc 1 1983, i^1983 ≡ 0 [ZMOD ∑ i in Finset.Icc 1 1983, i] := by
  native_decide