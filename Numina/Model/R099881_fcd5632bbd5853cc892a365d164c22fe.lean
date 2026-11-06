import Mathlib

theorem algebra_65234 (d c s t : ℝ)
    (hd : d = 200) (hc : c = 20) (hs : s = 20)
    (ht : t = 15 + 5 + 5 + 10) :
    min (min (min d (c / 4)) (s / 6)) (t / 3) ≤ 80 := by
  rw [hd, hc, hs, ht]
  norm_num [min_le_iff]
  all_goals norm_num