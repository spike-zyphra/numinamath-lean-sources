import Mathlib

theorem negated_algebra_45164 :
    {(x, y) : ℝ × ℝ | |x| + |y| = 1340 ∧ x^3 + y^3 + 2010 * x * y = 670^3} = 
    {(1005,-335), (-335,1005), (-670,-670)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Forward: both conditions hold implies (x, y) is one of the 3 solutions
    rintro ⟨h1, h2⟩
    by_cases hx1 : 0 ≤ x
    · -- Case where 0 ≤ x
      by_cases hy1 : 0 ≤ y
      · -- Case where 0 ≤ x and 0 ≤ y
        have eq1 : |x| + |y| = x + y := by 
          rw [abs_of_nonneg hx1, abs_of_nonneg hy1]
        rw [eq1] at h1
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - 670), sq_nonneg (y - 670), 
                  sq_nonneg (x + y - 1340)]
      · -- Case where 0 ≤ x and y < 0
        have eq1 : |x| + |y| = x - y := by 
          rw [abs_of_nonneg hx1, abs_of_neg (lt_of_not_ge hy1)]
          all_goals linarith
        rw [eq1] at h1
        have h3 : y = -335 := by
          nlinarith [sq_nonneg (x - 1005), sq_nonneg (y + 335), sq_nonneg (x - y), sq_nonneg (x + y + 335)]
        have h4 : x = 1005 := by 
          linarith
        simp [h4, h3]
    · -- Case where x < 0
      by_cases hy1 : 0 ≤ y
      · -- Case where x < 0 and 0 ≤ y
        have eq1 : |x| + |y| = -x + y := by 
          rw [abs_of_neg (lt_of_not_ge hx1), abs_of_nonneg hy1]
          all_goals linarith
        rw [eq1] at h1
        have h3 : x = -335 := by
          nlinarith [sq_nonneg (x + 335), sq_nonneg (y - 1005), sq_nonneg (x - y), sq_nonneg (x + y - 1340)]
        have h4 : y = 1005 := by 
          linarith
        simp [h3, h4]
      · -- Case where x < 0 and y < 0
        have eq1 : |x| + |y| = -x - y := by 
          rw [abs_of_neg (lt_of_not_ge hx1), abs_of_neg (lt_of_not_ge hy1)]
          all_goals linarith
        rw [eq1] at h1
        have h3 : x = -670 := by
          nlinarith [sq_nonneg (x + 670), sq_nonneg (y + 670), sq_nonneg (x - y), sq_nonneg (x + y + 1340)]
        have h4 : y = -670 := by 
          linarith
        simp [h3, h4]
  · -- Backward: (x, y) is one of the 3 solutions implies both conditions hold
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Check (1005, -335)
      constructor
      · -- Check |1005| + |-335| = 1340
        norm_num [abs_of_nonneg, abs_of_neg]
      · -- Check 1005^3 + (-335)^3 + 2010 * 1005 * (-335) = 670^3
        norm_num
    · -- Check (-335, 1005)
      constructor
      · -- Check |-335| + |1005| = 1340
        norm_num [abs_of_neg, abs_of_nonneg]
      · -- Check (-335)^3 + 1005^3 + 2010 * (-335) * 1005 = 670^3
        norm_num
    · -- Check (-670, -670)
      constructor
      · -- Check |-670| + |-670| = 1340
        norm_num [abs_of_neg, abs_of_neg]
      · -- Check (-670)^3 + (-670)^3 + 2010 * (-670) * (-670) = 670^3
        norm_num