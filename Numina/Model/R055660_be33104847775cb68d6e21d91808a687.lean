import Mathlib

theorem number_theory_136002 :
    ∑ n in (Finset.Icc 1 10).filter (fun n => Nat.Prime (n^9 + 3^(n+1)*n^6 + 3^(3*n))), n = 16 := by 
  native_decide