import Mathlib

theorem algebra_225109 (x : ℝ) (hx : x = 2 ^ ((1 : ℝ) / 3) + 3 ^ ((1 : ℝ) / 3)) :
    x ^ 9 - 15 * x ^ 6 - 87 * x ^ 3 - 125 = 0 := by
  have eq1 : x = (2 : ℝ) ^ ((1 : ℝ) / 3) + (3 : ℝ) ^ ((1 : ℝ) / 3) := by
    linarith [hx]
  have eq2 : x ^ 3 = 5 + 3 * ((2 : ℝ) ^ ((1 : ℝ) / 3) * (3 : ℝ) ^ ((1 : ℝ) / 3)) * x := by
    rw [eq1]
    have h1 : ((2 : ℝ) ^ ((1 : ℝ) / 3) + (3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 =
        ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + 3 * ((2 : ℝ) ^ ((1 : ℝ) / 3) * ((3 : ℝ) ^ ((1 : ℝ) / 3)) ) * ((2 : ℝ) ^ ((1 : ℝ) / 3) + (3 : ℝ) ^ ((1 : ℝ) / 3)) := by ring
    have h2 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h3 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    rw [h1, h2, h3]
    all_goals
      try norm_num
      all_goals
        try { 
          have h3 : (2 : ℝ) ^ ((1 : ℝ) / 3) * (3 : ℝ) ^ ((1 : ℝ) / 3) = (6 : ℝ) ^ ((1 : ℝ) / 3) := by
            have h4 : (2 : ℝ) ^ ((1 : ℝ) / 3) * (3 : ℝ) ^ ((1 : ℝ) / 3) = ((2 : ℝ) * (3 : ℝ)) ^ ((1 : ℝ) / 3) := by
              rw [← Real.mul_rpow]
              all_goals linarith
            have h5 : ((2 : ℝ) * (3 : ℝ)) ^ ((1 : ℝ) / 3) = (6 : ℝ) ^ ((1 : ℝ) / 3) := by norm_num
            rw [h4, h5]
          nlinarith [sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3) - (3 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3) * (3 : ℝ) ^ ((1 : ℝ) / 3) - (6 : ℝ) ^ ((1 : ℝ) / 3))]
        }
  have eq3 : ((2 : ℝ) ^ ((1 : ℝ) / 3) * (3 : ℝ) ^ ((1 : ℝ) / 3)) = (6 : ℝ) ^ ((1 : ℝ) / 3) := by
    have h4 : (2 : ℝ) ^ ((1 : ℝ) / 3) * (3 : ℝ) ^ ((1 : ℝ) / 3) = ((2 : ℝ) * (3 : ℝ)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.mul_rpow]
      all_goals linarith
    have h5 : ((2 : ℝ) * (3 : ℝ)) ^ ((1 : ℝ) / 3) = (6 : ℝ) ^ ((1 : ℝ) / 3) := by norm_num
    rw [h4, h5]
  have eq4 : x ^ 3 = 5 + 3 * ((6 : ℝ) ^ ((1 : ℝ) / 3)) * x := by 
    rw [eq2]
    have h3 : (2 : ℝ) ^ ((1 : ℝ) / 3) * (3 : ℝ) ^ ((1 : ℝ) / 3) = (6 : ℝ) ^ ((1 : ℝ) / 3) := eq3
    rw [h3]
  have eq5 : x ^ 9 - 15 * x ^ 6 - 87 * x ^ 3 - 125 = 0 := by
    have eq6 : x ^ 3 - 5 = 3 * ((6 : ℝ) ^ ((1 : ℝ) / 3)) * x := by
      linarith [eq4]
    have h_eq1 : (x ^ 3 - 5) ^ 3 = (3 * ((6 : ℝ) ^ ((1 : ℝ) / 3)) * x) ^ 3 := by
      rw [eq6]
    have eq7 : (x ^ 3 - 5) ^ 3 = x ^ 9 - 15 * x ^ 6 + 75 * x ^ 3 - 125 := by
      ring
    have eq8 : (3 * ((6 : ℝ) ^ ((1 : ℝ) / 3)) * x) ^ 3 = 27 * ((6 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 * x ^ 3 := by
      ring_nf
    have eq9 : ((6 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (6 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    rw [eq7, eq8, eq9] at h_eq1
    nlinarith [sq_nonneg (x ^ 3 - 5), sq_nonneg (x ^ 2), sq_nonneg (x * ((6 : ℝ) ^ ((1 : ℝ) / 3) )), sq_nonneg (x ^ 3 - 5 - 3 * ((6 : ℝ) ^ ((1 : ℝ) / 3)) * x), sq_nonneg (x ^ 3), Real.rpow_nonneg (show (0 : ℝ) ≤ (6 : ℝ) by norm_num) (1 / 3 : ℝ)]
  exact eq5