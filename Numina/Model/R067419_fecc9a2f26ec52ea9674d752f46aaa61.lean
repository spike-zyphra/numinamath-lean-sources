import Mathlib

theorem inequalities_224163 (x y z : ℝ) (h1 : x + y + z = 0) (h2 : abs x + abs y + abs z ≤ 1) :
    x + y / 2 + z / 3 ≤ 1 / 3 := by
  cases' abs_cases x <;> cases' abs_cases y <;> cases' abs_cases z <;> 
    linarith