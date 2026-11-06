import Mathlib

theorem algebra_295498 {a : ℝ} (ha : a > -7) (h : 1 / Real.sqrt (a + 7) + 1 / 7 = 19 / 84) :
    a = 137 := by
  have h1 : Real.sqrt (a + 7) > 0 := by
    apply Real.sqrt_pos.mpr
    linarith
  have h2 : 1 / Real.sqrt (a + 7) = 19 / 84 - 1 / 7 := by linarith
  have h3 : (19 / 84 : ℝ) - (1 / 7 : ℝ) = (1 / 12 : ℝ) := by 
    norm_num
  rw [h3] at h2
  have h4 : Real.sqrt (a + 7) = (12 : ℝ) := by
    field_simp at h2 ⊢ 
    all_goals nlinarith [Real.sqrt_pos.mpr (show a + 7 > 0 by linarith)]
  have h5 : a + 7 = (144 : ℝ) := by
    calc
      a + 7 = (Real.sqrt (a + 7)) ^ 2 := by
        rw [Real.sq_sqrt]
        all_goals linarith
      _ = (12 : ℝ) ^ 2 := by
        rw [h4]
      _ = (144 : ℝ) := by
        norm_num
  linarith
  all_goals
    norm_num
    all_goals try { nlinarith }