import Mathlib

theorem number_theory_95334 : (∏ i in (Finset.Ioo (-2015) 0).filter Odd, i) < 0 ∧ (∏ i in (Finset.Ioo (-2015) 0).filter Odd, i) % 10 = 5 := by
  native_decide