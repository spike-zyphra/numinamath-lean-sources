import Mathlib

theorem algebra_325530 :
    IsGreatest {z : ℝ | ∃ x y, z = x * y + 8 * x + y ∧ x ^ 2 + y ^ 2 = 20} 42 := by
  constructor
  · -- Show 42 is in the set
    use 4, 2
    all_goals norm_num
  · -- Show 42 is the greatest
    intro z h
    rcases h with ⟨x, y, h_eq, h_eq1⟩
    nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 2), sq_nonneg (x - 2), sq_nonneg (y - 4), 
      sq_nonneg (x + 4), sq_nonneg (y + 2), 
      sq_nonneg (x - y), sq_nonneg (x * y), sq_nonneg ((x + y))]