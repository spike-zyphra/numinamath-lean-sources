import Mathlib

theorem number_theory_189311 : ∑ i in Finset.range 1983, (i + 1) ^ 1983 ≡ 0 [ZMOD ∑ i in Finset.range 1983, (i + 1)] := by
  native_decide