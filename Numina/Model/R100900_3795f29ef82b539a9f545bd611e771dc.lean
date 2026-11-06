import Mathlib

theorem number_theory_207480 : (Nat.digits 10 ((10^2012 - 1) * (4 * 10^2011 + 1))).sum = 18108 := by
  native_decide