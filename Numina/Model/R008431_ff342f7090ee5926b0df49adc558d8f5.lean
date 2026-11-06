import Mathlib

theorem number_theory_15221 : ((Finset.Ioo 1996 4096).filter fun n => n % 900 = 200 ∨ n % 900 = 600).card = 5 := by
  native_decide