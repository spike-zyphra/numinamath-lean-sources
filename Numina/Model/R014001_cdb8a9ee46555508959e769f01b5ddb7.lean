import Mathlib

theorem inequalities_257344 (x y z : ℝ) :
    abs x + abs y + abs z - abs (x + y) - abs (y + z) - abs (z + x) +
    abs (x + y + z) ≥ 0 := by
  cases' abs_cases x with hx hx <;> cases' abs_cases y with hy hy <;> cases' abs_cases z with hz hz
  <;> cases' abs_cases (x + y) with hxy hxy <;> cases' abs_cases (y + z) with hyz hyz
  <;> cases' abs_cases (z + x) with hzx hzx <;> cases' abs_cases (x + y + z) with hxyz hxyz
  <;> all_goals
    linarith