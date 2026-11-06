import Mathlib

theorem number_theory_109761 : ∑ i ∈ Finset.range 20, 13^(i+1) ≡ 0 [ZMOD 7] := by
  native_decide