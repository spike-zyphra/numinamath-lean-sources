import Mathlib

theorem number_theory_14937 : ((Finset.Icc 1 1000).filter fun n => IsSquare (15 * n)).card = 8 := by
  native_decide