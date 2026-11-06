import Mathlib

theorem number_theory_97417 :
    ∑ x in (Finset.Icc 50 350).filter (fun y => y % 10 = 1), x = 5880 := by 
  native_decide