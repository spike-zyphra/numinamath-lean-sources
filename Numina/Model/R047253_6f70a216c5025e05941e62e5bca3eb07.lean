import Mathlib

theorem inequalities_255360 (x : ℝ) (hx : x > 0) :
    1 + x / 3 > (1 + x) ^ ((1 : ℝ) / 3) := by
  have h1 : (1 + x / 3) ^ 3 > 1 + x := by
    nlinarith [sq_pos_of_pos hx, sq_nonneg (x ^ 2), sq_nonneg (x + 3), sq_nonneg (x - 3), mul_pos hx hx]

  have h2 : ((1 + x) ^ ((1 : ℝ) / 3)) ^ 3 = 1 + x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith

  have h3 : (1 + x / 3) ^ 3 > ((1 + x) ^ ((1 : ℝ) / 3)) ^ 3 := by
    linarith [h1, h2]

  have h4 : 1 + x / 3 > (1 + x) ^ ((1 : ℝ) / 3) := by
    by_contra h
    push_neg at h 
    nlinarith [sq_nonneg ((1 + x / 3) - (1 + x) ^ ((1 : ℝ) / 3)), sq_nonneg ((1 + x / 3) ^ 2 - ((1 + x) ^ ((1 : ℝ) / 3)) ^ 2), sq_nonneg ((1 + x / 3) + ((1 + x) ^ ((1 : ℝ) / 3))), sq_nonneg (((1 + x) ^ ((1 : ℝ) / 3)) ^ 2 - (1 + x / 3) ^ 2), h3, h]

  exact h4