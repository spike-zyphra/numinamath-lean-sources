import Mathlib

/- Find the sum of the digits of the base-8 expression for $8888_{10}$. -/
theorem number_theory_19144 : (Nat.digits 8 8888).sum = 12 := by
  simp only [Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos, Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero, List.sum_cons, List.sum_nil, add_zero, Nat.reduceAdd, zero_add]