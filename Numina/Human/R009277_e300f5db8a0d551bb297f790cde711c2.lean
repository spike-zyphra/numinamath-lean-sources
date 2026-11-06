import Mathlib

/- There are approximately 0.4536 kilograms in a pound.  To the nearest whole pound, how many pounds does a steer that weighs 200 kg weigh? -/
theorem algebra_15713 {x : ℝ} (hx : x = 200 / 0.4536) : round x = 441 := by
  norm_num [hx, round_eq]