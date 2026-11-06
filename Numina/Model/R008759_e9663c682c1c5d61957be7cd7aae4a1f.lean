import Mathlib

theorem number_theory_55741 : (Finset.Icc 10 99).filter (fun n ↦ n^2 ≡ n [MOD 100]) = {25, 76} := by
  native_decide