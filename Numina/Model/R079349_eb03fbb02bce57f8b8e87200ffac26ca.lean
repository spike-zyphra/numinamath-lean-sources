import Mathlib

theorem algebra_5071 (A : Finset (ℝ × ℝ)) (hA : A = {(3, 10), (6, 20), (12, 35), (18, 40), (20, 50)}) :
    ∑ x in A.filter (fun y => y.2 > 2 * y.1 + 7), x.1 = 38 := by
  rw [hA]
  norm_num [Finset.sum_filter, Finset.sum_insert, Finset.sum_singleton]