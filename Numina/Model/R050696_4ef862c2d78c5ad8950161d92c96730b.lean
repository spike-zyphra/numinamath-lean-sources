import Mathlib

theorem number_theory_198025 : ∑ i in Finset.Icc 1 1000, i ≡ 0 [MOD 143] := by
  native_decide