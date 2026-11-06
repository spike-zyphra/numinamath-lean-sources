import Mathlib

theorem algebra_1493 {a b c : ℝ}
    (ha : a = ((-3.14 / 3.13) / 3.12)) (hb : b = ((2.14 / -2.13) / 2.12))
    (hc : c = ((1.14 / 1.13) / (-1.12))) : a > b ∧ b > c := by 
  rw [ha, hb, hc]
  norm_num