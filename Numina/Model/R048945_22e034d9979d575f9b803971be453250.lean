import Mathlib

theorem algebra_6225 : ∑ i ∈ Finset.range 20, (i + 1) * 21^i * 20^(19 - i) = 400 * 20^19 := by 
  native_decide