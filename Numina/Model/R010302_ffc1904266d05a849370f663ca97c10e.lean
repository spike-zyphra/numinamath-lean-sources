import Mathlib

theorem algebra_174668 (l : ℝ) (hl : l = 0.5) (k : ℝ) (hk : k = 200) (m : ℝ) (hm : m = 2) (g : ℝ) (hg : g = 10.0) :
    10 * l + 55 * m * g / k = 10.5 := by
  rw [hl, hk, hm, hg]
  norm_num