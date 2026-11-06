import Mathlib

theorem number_theory_277046 : ∏ i ∈ Finset.range 993, (2 * i + 1) + ∏ i ∈ Finset.range 993, (2 * i + 2) ≡ 0 [ZMOD 1987] := by 
  native_decide