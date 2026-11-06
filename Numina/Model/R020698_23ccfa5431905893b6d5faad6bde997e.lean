import Mathlib

theorem inequalities_83457 (x y z : ℝ) :
    |x| + |y| + |z| - |x + y| - |y + z| - |z + x| + |x + y + z| ≥ 0 := by
  cases' abs_cases x with hx hx
  <;> cases' abs_cases y with hy hy
  <;> cases' abs_cases z with hz hz
  <;> cases' abs_cases (x + y) with hxy hxy
  <;> cases' abs_cases (y + z) with hyz hyz
  <;> cases' abs_cases (z + x) with hzx hzx
  <;> cases' abs_cases (x + y + z) with h h
  <;> all_goals linarith