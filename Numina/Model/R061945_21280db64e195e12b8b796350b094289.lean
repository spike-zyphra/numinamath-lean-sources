import Mathlib

theorem number_theory_109785 : ∑ i ∈ Finset.range 12, 2^(2 * i + 1) ≡ 0 [ZMOD 105] := by 
  native_decide