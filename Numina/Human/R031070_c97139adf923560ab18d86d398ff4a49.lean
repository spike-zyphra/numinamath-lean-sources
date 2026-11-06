import Mathlib

/- Find the sum of all the rational terms in the expansion of \[(\sqrt{2} + \sqrt[3]{3})^{12}.\] -/
theorem algebra_21413 : ∑ n in Finset.range 3, (Nat.choose 12 (6 * n)) * (2 ^ (3 * (2 - n))) * (3 ^ (2 * n)) = 66673 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right, Nat.choose, Nat.factorial]
  norm_num
  