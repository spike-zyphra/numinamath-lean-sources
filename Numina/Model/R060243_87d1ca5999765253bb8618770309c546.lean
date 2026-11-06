import Mathlib

theorem number_theory_183756 :
    (∑ i in Finset.Icc 1 100, if Even i then i^2 else 0) -
    (∑ i in Finset.Ico 1 100, if Odd i then i^2 else 0) = 5050 := by
  native_decide