import Mathlib

  theorem number_theory_263061 : 
    ∑ n in Finset.Icc 1 6786, (Nat.digits 10 n).length = 26037 := by native_decide