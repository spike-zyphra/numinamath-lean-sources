import Mathlib

open Real

theorem algebra_3477 {line gry point : ℝ} (hl : line = 1 / 12) (hg : gry = line / 10)
    (hp : point = 1 / 72) : (0.50 * gry ^ 2) / point ^ 2 = 0.18 := by
  have hg' : gry = 1 / 120 := by
    rw [hg, hl]
    norm_num
  have hp' : point = 1 / 72 := hp
  rw [hg', hp']
  norm_num