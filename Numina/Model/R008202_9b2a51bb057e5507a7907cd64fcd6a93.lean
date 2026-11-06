import Mathlib

theorem algebra_14557 (jay paul : ℝ) (hjay : jay = 0.75 / 15 * 60) (hpaul : paul = 2.5 / 30 * 60) :
    1.5 * (jay + paul) = 12 := by
  rw [hjay, hpaul]
  norm_num