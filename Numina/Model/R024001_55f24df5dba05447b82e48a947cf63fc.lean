import Mathlib

theorem algebra_624 (a b c t : ℕ) (ha : a = t * 44 / 100) (hb : b = t * 41 / 100) (hc : c = t - a - b) (ht : t = 246000) : |(a : ℤ) - c| = 71340 := by
  subst ht
  norm_num [ha, hb, hc]
  <;> rfl