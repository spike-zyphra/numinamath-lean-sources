import Mathlib

theorem number_theory_4985 : ((Finset.range 2022).filter fun n => 13 ∣ (n + 1) ∨ 17 ∣ (n + 1)).card = 264 := by 
  native_decide