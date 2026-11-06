import Mathlib

theorem number_theory_15789 :
    ∑ n in (Finset.Icc 10 99).filter (fun n => n^2 ≡ 1 [MOD 100]), n = 199 := by 
  native_decide