import Mathlib

theorem algebra_6040 : (∑ i ∈ Finset.range 100, (i * 5 + 2)) % 1000 = 950 := by 
  native_decide