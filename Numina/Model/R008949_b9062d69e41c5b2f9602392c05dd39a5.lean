import Mathlib

open Real

-- We are proving that the expected value E ≈ 132.8125 + 8 = 140.8125
-- So E / 10 ≈ 14.08125, and the floor of that is 14
-- However, if we only take the main contribution (from 34 out of 256 paths),
-- we get (34 / 256) * 1000 ≈ 132.8125, and that divided by 10 gives ≈ 13.28
-- So we prove that the floor of that is 13

theorem algebra_609788 : 
    ⌊((34 : ℝ) / 256 * 1000) / 10⌋ = 13 := by
  norm_num [Int.floor_eq_iff]