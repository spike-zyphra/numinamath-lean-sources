import Mathlib

theorem algebra_608440 : IsGreatest {r | ∃ x y : ℝ, (x - 4) ^ 2 / 4 + y ^ 2 / 9 = 1 ∧ r = x ^ 2 / 4 + y ^ 2 / 9} 9 := by
  constructor
  · -- Show 9 is in the set
    use 6, 0
    constructor
    · -- Check the constraint
      norm_num
    · -- Check r = 9
      norm_num
  · -- Show that 9 is greatest in the set
    intro r
    rintro ⟨x, y, h_eq, hr⟩
    nlinarith [sq_nonneg (x - 6), sq_nonneg (y), sq_nonneg (x - 2), sq_nonneg (y), sq_nonneg ((x - 4) * 9 - 4 * y ^ 2), sq_nonneg (x - 4), sq_nonneg (x * 4 - 2 * 9)]