import Mathlib

theorem number_theory_208889 :
    ∑ n in (Finset.Icc 1 200).filter (fun n => n % 11 = 7 ∧ n % 7 = 5), n = 351 := by
  native_decide