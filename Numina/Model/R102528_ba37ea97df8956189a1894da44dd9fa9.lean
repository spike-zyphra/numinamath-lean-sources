import Mathlib

theorem algebra_3881 : 4 * ∑ i ∈ Finset.range 15, (i + 1) ^ 3 + 6 * ∑ i ∈ Finset.range 15, (i + 1) ^ 2 + 4 * ∑ i ∈ Finset.range 15, (i + 1) + 15 = 65535 := by 
  native_decide