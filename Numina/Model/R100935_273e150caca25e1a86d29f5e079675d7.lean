import Mathlib

theorem algebra_250154 (Sblack Swhite : ℕ)
    (hSblack : Sblack = ∑ i ∈ Finset.range 8, ∑ j ∈ Finset.range 8,
      if (i + j) % 2 = 0 then (i + 1) + (j + 1) else 0)
    (hSwhite : Swhite = ∑ i ∈ Finset.range 8, ∑ j ∈ Finset.range 8,
      if (i + j) % 2 ≠ 0 then (i + 1) + (j + 1) else 0) :
    Sblack = 288 := by 
  rw [hSblack]
  norm_num [Finset.sum_range_succ]