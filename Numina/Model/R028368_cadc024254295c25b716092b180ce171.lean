import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_301453 :
  IsGreatest {z : ℝ | ∃ x y, z = x^2 - x * y + y^2 ∧ |x| + |y| ≤ 1} 1 := by
  constructor
  · -- Show 1 is in the set
    use 1, 0
    norm_num
  · -- Show 1 is the greatest in the set
    intro z h
    rcases h with ⟨x, y, h_eq, h_le⟩
    cases' abs_cases x with hx hx <;> 
    cases' abs_cases y with hy hy
    all_goals 
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 1), sq_nonneg (y - 1),
        sq_nonneg (x + y - 1)]