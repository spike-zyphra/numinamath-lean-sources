import Mathlib

theorem number_theory_2968 :
    ∑ n in (Finset.Icc 10 99).filter (fun n => 13 ∣ (10 ^ n + 1)), n = 855 := by 
  native_decide