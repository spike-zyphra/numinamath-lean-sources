import Mathlib

theorem calculus_13202 (a b c d : ℝ) (ha : a = 3) (hb : b = -7) (hc : c = -6) (hd : d = 11) :
    (a + c, b + d) = (-3, 4) := by
  simp [Prod.ext_iff, ha, hb, hc, hd]
  all_goals norm_num