import Mathlib

theorem algebra_10570 {x : ℝ} (hx : x = (4 : ℝ) ^ ((1 : ℝ) / 3) + (2 : ℝ) ^ ((1 : ℝ) / 3) + 1) :
    (1 + 1 / x) ^ 3 = 2 := by

  have ha1 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith

  have ha2 : ((4 : ℝ) ^ ((1 : ℝ) / 3)) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
    have h1 : (4 : ℝ) ^ ((1 : ℝ) / 3) = ((2 : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 3) := by 
      have h11 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
      rw [h11]
    have h2 : ((2 : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 3) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by 
      have h31 : ((2 : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ (2 * (1 / 3 : ℝ) ) := by
        rw [← Real.rpow_mul]
        ring
        all_goals linarith
      have h32 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = (2 : ℝ) ^ (2 * (1 / 3 : ℝ) ) := by
        have h41 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = (2 : ℝ) ^ (2 * (1 / 3 : ℝ) ) := by
          have h42 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = (2 : ℝ) ^ (2 * (1 / 3 : ℝ) ) := by
            have h51 : (2 : ℝ) ^ (2 * (1 / 3 : ℝ) ) = ((2 : ℝ) ^ ((1 / 3 : ℝ)) ) ^ 2 := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul]
              ring
              all_goals linarith
            rw [h51]
          exact h42
        exact h41
      rw [h31, h32]
    rw [h1]
    exact h2

  have hx2 : x = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 + (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 := by
    rw [hx]
    rw [ha2]

  have h1 : x ≠ 0 := by
    rw [hx2]
    have h2 : (2 : ℝ) ^ ((1 : ℝ) / 3) > 0 := by positivity
    nlinarith [sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3)), h2]

  have h2 : 1 / x = ( (2 : ℝ) ^ ((1 : ℝ) / 3) - 1 ) := by
    rw [hx2]
    have h3 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 + (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 ≠ 0 := by
      have h2 : (2 : ℝ) ^ ((1 : ℝ) / 3) > 0 := by positivity
      nlinarith [sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3)), h2]
    field_simp
    nlinarith [sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1), sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3) + 1), 
      Real.rpow_pos_of_pos (show 0 < (2 : ℝ) by norm_num) (1 / 3), ha1]

  have h3 : 1 + 1 / x = (2 : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [h2]
    ring

  rw [h3]
  have ha4 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith
  exact ha4