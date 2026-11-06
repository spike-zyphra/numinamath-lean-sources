import Mathlib

theorem algebra_605308 : {((x : ℝ), (y : ℝ)) | abs x + abs y = 1340 ∧ x^3 + y^3 + 2010 * x * y = 670^3} = {(-670, -670), (1005, -335), (-335, 1005)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) satisfy |x| + |y| = 1340 and x^3 + y^3 + 2010xy = 670^3, prove (x, y) ∈ {(-670, -670), (1005, -335), (-335, 1005)}
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases hx1 : x ≥ 0
    · -- case x ≥ 0
      by_cases hy1 : y ≥ 0
      · -- case y ≥ 0
        rw [abs_of_nonneg hx1, abs_of_nonneg hy1] at h1
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 670), sq_nonneg (x - 670), sq_nonneg (y - 670)]
      · -- case y < 0
        rw [abs_of_nonneg hx1, abs_of_neg (lt_of_not_ge hy1)] at h1
        have h3 : y = x - 1340 := by linarith
        rw [h3] at h2
        have h4 : x = 1005 := by
          nlinarith [sq_nonneg (x - 1005), sq_nonneg (x + 335), sq_nonneg (x - 335), sq_nonneg (x * (x - 1005)), sq_nonneg ((x - 1005) * (x + 335))]
        have h5 : y = -335 := by
          linarith [h3, h4]
        simp [h4, h5]
    · -- case x < 0
      by_cases hy1 : y ≥ 0
      · -- case y ≥ 0
        rw [abs_of_neg (lt_of_not_ge hx1), abs_of_nonneg hy1] at h1
        have h3 : x = y - 1340 := by linarith
        rw [h3] at h2
        have h4 : y = 1005 := by
          nlinarith [sq_nonneg (y - 1005), sq_nonneg (y + 335), sq_nonneg (y - 335), sq_nonneg (y * (y - 1005)), sq_nonneg ((y - 1005) * (y + 335))]
        have h5 : x = -335 := by
          linarith [h3, h4]
        simp [h5, h4]
      · -- case y < 0
        rw [abs_of_neg (lt_of_not_ge hx1), abs_of_neg (lt_of_not_ge hy1)] at h1
        have h3 : x = -670 := by
          nlinarith [sq_nonneg (x + 670), sq_nonneg (y + 670), sq_nonneg (x - y), sq_nonneg (x + y + 670), sq_nonneg ((x + 670) * (y + 670))]
        have h4 : y = -670 := by
          nlinarith [sq_nonneg (x + 670), sq_nonneg (y + 670), sq_nonneg (x - y), sq_nonneg (x + y + 670), sq_nonneg ((x + 670) * (y + 670))]
        simp [h3, h4]
  · -- Show that each of the given solutions satisfies both equations
    rintro (h | h | h)
    · -- First solution (-670, -670)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- Check the first equation
        norm_num [abs_of_nonpos]
      · -- Check the second equation
        norm_num
    · -- Second solution (1005, -335)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- Check the first equation
        norm_num [abs_of_nonneg, abs_of_neg]
      · -- Check the second equation
        norm_num
    · -- Third solution (-335, 1005)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- Check the first equation
        norm_num [abs_of_nonpos, abs_of_nonneg]
      · -- Check the second equation
        norm_num