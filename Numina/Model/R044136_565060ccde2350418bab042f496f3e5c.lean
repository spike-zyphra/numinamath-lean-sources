import Mathlib

theorem number_theory_23133 :
    ∑ n in (Finset.Ico 1 50).filter (fun n => n % 8 = 5 ∧ n % 6 = 3), n = 66 := by 
  native_decide