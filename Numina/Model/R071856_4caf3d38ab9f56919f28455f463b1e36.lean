import Mathlib

theorem algebra_195156 (a d : ℤ) (ha : 0 < a) (hd : 0 < d)
    (hsum : ∑ i ∈ Finset.range 10, (a + d * i) = 55)
    (hdiff : ∑ i ∈ Finset.range 5, ((a + d * (2 * i)) - (a + d * (2 * i - 1))) = d) :
    d = 16 := by
  norm_num [Finset.sum_range_succ] at hsum hdiff
  linarith