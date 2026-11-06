import Mathlib

theorem number_theory_205956 :
    (∑ i in Finset.range 39, if (Nat.choose 38 i) % 3 = 1 then 1 else 0) -
    (∑ i in Finset.range 39, if (Nat.choose 38 i) % 3 = 2 then 1 else 0) = 4 := by 
  native_decide