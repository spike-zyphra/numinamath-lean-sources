import Mathlib

theorem number_theory_16196 : ((Finset.range 1000).filter fun n => n % 11 = 6).card = 91 := by
  native_decide