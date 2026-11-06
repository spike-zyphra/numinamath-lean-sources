import Mathlib

theorem number_theory_110063 :
    ∑ n in (Finset.Icc 100 999).filter (fun x => 7 ∣ x), n = 70336 := by 
  native_decide