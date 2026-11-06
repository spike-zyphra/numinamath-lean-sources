import Mathlib

theorem number_theory_208867 : ∏ i ∈ Finset.Icc 1 1001, i + ∏ i ∈ Finset.Icc 1002 2002, i ≡ 0 [ZMOD 2003] := by
  native_decide