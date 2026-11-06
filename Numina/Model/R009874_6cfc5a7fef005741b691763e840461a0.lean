import Mathlib

theorem number_theory_11122 : (Finset.range 101).filter fun n => 100 * n % 101 = 72 = {29} := by
  native_decide