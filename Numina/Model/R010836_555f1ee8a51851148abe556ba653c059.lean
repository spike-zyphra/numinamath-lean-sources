import Mathlib

theorem algebra_14058 : ∑ x in (Finset.Ico 1 62).filter Even, x = 930 := by
  native_decide