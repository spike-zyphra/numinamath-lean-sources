import Mathlib

theorem number_theory_90775 : ∑ i in Finset.range 2018, (i + 1) ≡ 0 [ZMOD 3] := by
  native_decide