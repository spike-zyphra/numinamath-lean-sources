import Mathlib

theorem algebra_10392 (descent ascent : ℝ) (hd : descent = ∑ i ∈ Finset.range 3, 16 * (3 / 4) ^ i)
    (ha : ascent = ∑ i ∈ Finset.range 3, 16 * (3 / 4) ^ (i + 1)) :
    round (descent + ascent) = 65 := by
  rw [hd, ha]
  norm_num [Finset.sum_range_succ, round_eq]
  <;> norm_num -- To handle arithmetic expressions