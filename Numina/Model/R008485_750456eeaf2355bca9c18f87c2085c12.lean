import Mathlib

theorem algebra_15244 (l w h : ℝ) (hl : l = 24) (hw : w = 32) (hh : h = 18 / 12)
    (p : ℝ) (hp : p = 3 * 8) (g : ℝ) (hg : g = 7.5) :
    (l * w * h) / (p / g) = 360 := by
  rw [hl, hw, hh, hp, hg]
  norm_num