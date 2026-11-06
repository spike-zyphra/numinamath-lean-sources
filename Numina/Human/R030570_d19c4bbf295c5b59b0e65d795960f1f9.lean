import Mathlib

theorem number_theory_114610 (h:100^10 = ∑ i ∈ Finset.range n, 10) : n = 10^19 := by
  norm_num at h ⊢
  nlinarith
