import Mathlib

theorem algebra_287417 {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h1 : Real.sqrt x + Real.sqrt y = 10) (h2 : x ^ ((1 : ℝ) / 4) + y ^ ((1 : ℝ) / 4) = 4) :
    x * y = 81 := by

  have h3 : (x ^ ((1 : ℝ) / 4)) ^ 4 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith

  have h4 : (y ^ ((1 : ℝ) / 4)) ^ 4 = y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith

  have h5 : Real.sqrt x = (x ^ ((1 : ℝ) / 4)) ^ 2 := by
    have h5a : Real.sqrt x = ((x ^ ((1 : ℝ) / 4)) ^ 2) := by
      have h7 : (x ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt x := by
        have h8 : (x ^ ((1 : ℝ) / 4)) ^ 2 = (x ^ ((1 / 2) : ℝ)) := by
          have h9 : (x ^ ((1 : ℝ) / 4)) ^ 2 = x ^ ((1 / 2 : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            norm_num
            all_goals linarith
          linarith [h9]
        have h9 : x ^ ((1 / 2 : ℝ)) = Real.sqrt x := by
          rw [Real.sqrt_eq_rpow]
        rw [h8, h9]
      linarith [h7]
    linarith [h5a]

  have h6 : Real.sqrt y = (y ^ ((1 : ℝ) / 4)) ^ 2 := by
    have h6a : Real.sqrt y = ((y ^ ((1 : ℝ) / 4)) ^ 2) := by
      have h7 : (y ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt y := by
        have h8 : (y ^ ((1 : ℝ) / 4)) ^ 2 = (y ^ ((1 / 2) : ℝ)) := by
          have h9 : (y ^ ((1 : ℝ) / 4)) ^ 2 = y ^ ((1 / 2 : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            norm_num
            all_goals linarith
          linarith [h9]
        have h9 : y ^ ((1 / 2 : ℝ)) = Real.sqrt y := by
          rw [Real.sqrt_eq_rpow]
        rw [h8, h9]
      linarith [h7]
    linarith [h6a]

  have eq1 : ((x ^ ((1 : ℝ) / 4)) ^ 2 + (y ^ ((1 : ℝ) / 4)) ^ 2) = 10 := by
    have h7 : (x ^ ((1 : ℝ) / 4)) ^ 2 + (y ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt x + Real.sqrt y := by
      rw [h5, h6]
    linarith [h7, h1]

  have eq2 : (x ^ ((1 : ℝ) / 4)) + (y ^ ((1 : ℝ) / 4)) = (4 : ℝ) := by
    linarith [h2]

  have eq3 : (x ^ ((1 : ℝ) / 4)) * (y ^ ((1 : ℝ) / 4)) = 3 := by
    have h8 : ((x ^ ((1 : ℝ) / 4)) + (y ^ ((1 : ℝ) / 4))) ^ 2 = ((x ^ ((1 : ℝ) / 4)) ^ 2 + (y ^ ((1 : ℝ) / 4)) ^ 2) + 2 * ((x ^ ((1 : ℝ) / 4)) * (y ^ ((1 : ℝ) / 4)) ) := by
      ring
    rw [eq1, eq2] at h8
    nlinarith

  calc
    x * y = ((x ^ ((1 : ℝ) / 4)) ^ 4) * ((y ^ ((1 : ℝ) / 4)) ^ 4) := by
      rw [h3, h4]
    _ = (((x ^ ((1 : ℝ) / 4) ) * (y ^ ((1 : ℝ) / 4) ) ) ^ 4) := by
      ring
    _ = (3 : ℝ) ^ 4 := by
      rw [eq3]
    _ = (81 : ℝ) := by
      norm_num