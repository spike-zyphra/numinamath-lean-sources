import Mathlib

theorem algebra_85760 {A B : ℤ}
    (hA : A = ∑ i ∈ Finset.range 19, (2 * i + 1) * (2 * i + 2) + 39)
    (hB : B = 1 + ∑ i ∈ Finset.range 19, (2 * i + 2) * (2 * i + 3)) :
    |A - B| = 722 := by
  rw [hA, hB]
  norm_num [Finset.sum_range_succ]