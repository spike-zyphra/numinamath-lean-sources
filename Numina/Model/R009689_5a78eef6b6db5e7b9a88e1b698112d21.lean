import Mathlib

theorem algebra_13107 : ((Finset.range 6).powerset.filter fun s => s.card = 1 ∨ s.card = 2).card = 21 := by 
  native_decide