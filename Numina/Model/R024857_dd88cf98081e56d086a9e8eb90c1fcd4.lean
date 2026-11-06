import Mathlib

theorem algebra_166041 (x : ℝ) (hx : x > 0) (h : 8 * 10 ^ 8 * x ^ (-3 / 2 : ℝ) = 800) :
    x ≥ 10 ^ 4 := by
  have eq1 : x ^ (-3 / 2 : ℝ) = 1 / 1000000 := by
    have eq2 : x ^ (-3 / 2 : ℝ) = 1 / 1000000 := by
      norm_num at h ⊢
      nlinarith [h, Real.rpow_pos_of_pos hx (-3 / 2 : ℝ)]
    exact_mod_cast eq2

  have h1 : x ≥ 10 ^ 4 := by
    have eq2 : x = (10 : ℝ) ^ 4 := by
      have eq3 : x ^ (-3 / 2 : ℝ) = 1 / 1000000 := eq1
      have eq4 : x ^ (3 / 2 : ℝ) = 1000000 := by
        have eq5 : x ^ (-3 / 2 : ℝ) = 1 / 1000000 := eq1
        have eq6 : x ^ (3 / 2 : ℝ) = 1000000 := by
          have eq7 : x ^ (3 / 2 : ℝ) = (x ^ (-3 / 2 : ℝ))⁻¹ := by
            rw [← Real.rpow_neg]
            norm_num
            all_goals linarith
          rw [eq7, eq5]
          norm_num
        exact_mod_cast eq6
      have eq7 : x = 10000 := by
        have eq8 : x ^ (3 / 2 : ℝ) = 1000000 := eq4
        have eq9 : x ^ (3 / 2 : ℝ) = ((x) ^ (1 / 2 : ℝ)) ^ 3 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf
          all_goals linarith
        rw [eq9] at eq8
        have eq10 : (x) ^ (1 / 2 : ℝ) = 100 := by
          have eq11 : ((x) ^ (1 / 2 : ℝ)) ^ 3 = 1000000 := eq8
          have eq12 : ((x) ^ (1 / 2 : ℝ)) ^ 3 - 1000000 = 0 := by linarith
          have eq13 : ((x) ^ (1 / 2 : ℝ) - 100) * (((x) ^ (1 / 2 : ℝ)) ^ 2 + 100 * ((x) ^ (1 / 2 : ℝ)) + 10000) = 0 := by
            nlinarith
          cases' (mul_eq_zero.mp eq13) with eq14 eq15
          · -- Case where (x) ^ (1 / 2 : ℝ) - 100 = 0, so x = 100
            linarith
          · -- Case where ((x) ^ (1 / 2 : ℝ)) ^ 2 + 100 * ((x) ^ (1 / 2 : ℝ)) + 10000 = 0
            nlinarith [sq_nonneg ((x) ^ (1 / 2 : ℝ) + 50), Real.rpow_nonneg (show (0 : ℝ) ≤ x by linarith) (1 / 2)]
        have eq11 : x = (x ^ (1 / 2 : ℝ)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals linarith
        rw [eq10] at eq11
        nlinarith
      norm_num at eq7 ⊢
      linarith
    norm_num at eq2 ⊢
    linarith
  linarith [h1]