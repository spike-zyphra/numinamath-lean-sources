import Mathlib

theorem number_theory_309350 : (∑ i ∈ Finset.range 2010, (1 / (i + 1))) * 2011 ≡ 0 [ZMOD 2011] := by 
  native_decide