import Mathlib

theorem number_theory_3091 : (∑ i in Finset.range 8, (Nat.choose 16 (2 * i)) * 39^(2 * i) + 39^(2 * 8)) % 100 = 8 := by
  native_decide