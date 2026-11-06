import Mathlib

open Real

theorem algebra_15073 (x : ℝ) (hx : 4 * x = 2 * π * 2) : (round (100 * x) / 100 : ℝ) = 3.14 := by

  have h1 : x = π := by
    linarith

  rw [h1]

  have h2 : round (100 * π) = 314 := by
    rw [round_eq]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> try nlinarith [pi_gt_31415, pi_lt_31416]

  rw [h2]
  norm_num