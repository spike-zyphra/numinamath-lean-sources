import Mathlib


theorem algebra_3609 {A : ℝ} (h : (2017:ℝ) / 326 = 6 + 1 / (5 + 1 / (A + 1 / (1 + 1 / (9 + 1 / 2))))) :
    A = 2 := by
  have h21 : 9 + 1 / 2 = (19 / 2 : ℝ) := by norm_num
  have h22 : 1 + 1 / (9 + 1 / 2 : ℝ) = (21 / 19 : ℝ) := by
    rw [h21]
    norm_num
  have h23 : A + 1 / (1 + 1 / (9 + 1 / 2 : ℝ)) = A + (19 / 21 : ℝ) := by
    rw [h22]
    field_simp
  have h34 : (2017:ℝ) / 326 = 6 + 1 / (5 + 1 / (A + 1 / (1 + 1 / (9 + 1 / 2)) )) := by
    linarith [h]
  rw [show A + 1 / (1 + 1 / (9 + 1 / 2 : ℝ)) = A + (19 / 21 : ℝ) by linarith [h23] ] at h34
  have h35 : 5 + 1 / (A + (19 / 21 : ℝ)) ≠ 0 := by
    by_contra h350
    have h360 : 1 / (5 + 1 / (A + (19 / 21 : ℝ)) ) = (0 : ℝ) := by
      rw [show 5 + 1 / (A + (19 / 21 : ℝ)) = (0 : ℝ) by linarith [h350]]
      norm_num
    have h370 : (2017:ℝ) / 326 = 6 := by
      linarith [h34, h360]
    norm_num at h370
  have h390 : 1 / (5 + 1 / (A + (19 / 21 : ℝ)) ) = (61 / 326 : ℝ) := by
    have h380 : 1 / (5 + 1 / (A + (19 / 21 : ℝ)) ) = (2017:ℝ) / 326 - 6 := by
      linarith [h34]
    rw [h380]
    norm_num
  have h400 : 5 + 1 / (A + (19 / 21 : ℝ)) = (326 / 61 : ℝ) := by
    have h3900 : 1 / (5 + 1 / (A + (19 / 21 : ℝ)) ) = (61 / 326 : ℝ) := by
      linarith [h390]
    have h440 : (5 + 1 / (A + (19 / 21 : ℝ)) ) ≠ 0 := h35
    have h450 : 5 + 1 / (A + (19 / 21 : ℝ)) = (326 / 61 : ℝ) := by
      have eq1 : (1 / (5 + 1 / (A + (19 / 21 : ℝ)) ) ) = (61 / 326 : ℝ) := by
        linarith [h3900]
      have eq2 : 5 + 1 / (A + (19 / 21 : ℝ)) ≠ 0 := h35
      have eq3 : (5 + 1 / (A + (19 / 21 : ℝ)) ) = 1 / ((1 / (5 + 1 / (A + (19 / 21 : ℝ)) )) ) := by
        field_simp [show (5 + 1 / (A + (19 / 21 : ℝ)) ) ≠ 0 by assumption]
      rw [eq3, eq1]
      all_goals
        norm_num
    linarith
  have h460 : 1 / (A + (19 / 21 : ℝ)) = (21 / 61 : ℝ) := by
    have h470 : 5 + 1 / (A + (19 / 21 : ℝ)) = (326 / 61 : ℝ) := h400
    have h480 : 1 / (A + (19 / 21 : ℝ)) = (326 / 61 - 5 : ℝ) := by
      linarith [h470]
    rw [h480]
    norm_num
  have h490 : A + (19 / 21 : ℝ) ≠ 0 := by
    by_contra h0
    have h190 : 1 / (A + (19 / 21 : ℝ)) = 0 := by
      rw [show A + (19 / 21 : ℝ) = (0 : ℝ) by linarith [h0]]
      norm_num
    linarith [h460, h190]
  have h500 : A + (19 / 21 : ℝ) = (61 / 21 : ℝ) := by
    have h510 : 1 / (A + (19 / 21 : ℝ)) = (21 / 61 : ℝ) := h460
    have h520 : A + (19 / 21 : ℝ) ≠ 0 := h490
    have h530 : A + (19 / 21 : ℝ) = 1 / ((1 / (A + (19 / 21 : ℝ)) ) ) := by
      field_simp [show A + (19 / 21 : ℝ) ≠ 0 by assumption]
    rw [h530, h510]
    all_goals
      norm_num
  linarith