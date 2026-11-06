import Mathlib

/-The discriminant of the quadratic equation $x^{2}-4x+3=0$ is ____.-/
theorem algebra_9084 (a b c : ℝ) (ha : a = 1) (hb : b = -4) (hc : c = 3) : discrim a b c = 4 := by
  rw [discrim, ha, hb, hc]
  norm_num