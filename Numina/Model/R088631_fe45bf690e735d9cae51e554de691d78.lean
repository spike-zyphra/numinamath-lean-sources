import Mathlib

theorem number_theory_111178 : (∏ i in Finset.Icc 1 70, i) + 1234 ≡ 1234 [ZMOD 2013] := by 
  native_decide