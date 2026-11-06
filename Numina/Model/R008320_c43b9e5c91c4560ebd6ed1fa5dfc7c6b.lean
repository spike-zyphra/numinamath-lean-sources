import Mathlib

theorem number_theory_15533 : ((Finset.Icc 1 100).filter fun n => (2 ∣ n ∨ 3 ∣ n) ∧ ¬4 ∣ n).card = 42 := by 
  native_decide