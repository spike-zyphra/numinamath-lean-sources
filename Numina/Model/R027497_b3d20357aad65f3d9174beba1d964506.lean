import Mathlib

theorem algebra_10765 {x : ℝ} (hx : x > 0) (h : x + 1 / x = 98) :
    Real.sqrt x + 1 / Real.sqrt x = 10 := by
  have h1 : Real.sqrt x > 0 := by
    apply Real.sqrt_pos.2
    linarith
  have h2 : (Real.sqrt x + 1 / Real.sqrt x) ^ 2 = 100 := by
    have h3 : (Real.sqrt x + 1 / Real.sqrt x) ^ 2 = x + 1 / x + 2 := by
      field_simp [h1]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
    rw [h3, h]
    all_goals norm_num
  have h3 : Real.sqrt x + 1 / Real.sqrt x > 0 := by
    have h4 : Real.sqrt x > 0 := h1
    have h5 : 1 / Real.sqrt x > 0 := by
      apply one_div_pos.mpr
      linarith
    linarith
  have h4 : Real.sqrt x + 1 / Real.sqrt x = 10 := by
    nlinarith [h2, h3]
  exact h4