import Mathlib

theorem number_theory_194454 : ((Finset.Icc 1 100).filter (fun n => ¬(2 ∣ n) ∧ ¬(3 ∣ n) ∧ ¬(5 ∣ n))).card = 26 := by 
  native_decide