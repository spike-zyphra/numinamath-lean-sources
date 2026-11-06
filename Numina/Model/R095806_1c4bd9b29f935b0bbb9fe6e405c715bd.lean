import Mathlib

theorem algebra_309019 :
    IsGreatest {z : ℝ | ∃ x y, z = x^2 - x * y + y^2 ∧ x^2 + x * y + y^2 = 3} 9 ∧
    IsLeast {z : ℝ | ∃ x y, z = x^2 - x * y + y^2 ∧ x^2 + x * y + y^2 = 3} 1 := by

  constructor
  · -- Show that 9 is the greatest element in the set
    constructor
    · -- Show that 9 is in the set
      use Real.sqrt 3, -Real.sqrt 3
      constructor
      · -- Compute the value of the function at these points
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      · -- Check the constraint
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    · -- Show that for all z in the set, z ≤ 9
      intro z hz
      rcases hz with ⟨x, y, h_eq, h_const⟩
      nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x + Real.sqrt 3), sq_nonneg (y - Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  · -- Show that 1 is the least element in the set
    constructor
    · -- Show that 1 is in the set
      use (1 : ℝ), (1 : ℝ)
      constructor
      · -- Compute the value of the function at these points
        norm_num
      · -- Check the constraint
        norm_num
    · -- Show that for all z in the set, z ≥ 1
      intro z hz
      rcases hz with ⟨x, y, h_eq, h_const⟩
      nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x + Real.sqrt 3), sq_nonneg (y - Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]