import Mathlib

theorem algebra_52619 :
    IsGreatest {z : ℝ | ∃ x y : ℝ, x + y + z = 5 ∧ x * y + y * z + x * z = 3} (13 / 3) := by
  constructor
  · -- Show that 13/3 is in the set
    use 1 / 3, 1 / 3
    constructor
    · -- Check that 1/3 + 1/3 + 13/3 = 5
      norm_num
    · -- Check that (1/3)*(1/3) + (1/3)*(13/3) + (1/3)*(13/3) = 3
      norm_num
  · -- Show that 13/3 is the greatest element in the set
    intro z h
    rcases h with ⟨x, y, h1, h2⟩
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2 * z), sq_nonneg (x - y), sq_nonneg (x + y - z)]