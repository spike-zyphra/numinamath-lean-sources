import Mathlib

theorem algebra_13343 {x : ℝ} (hx : x ≠ 0) (h : Real.sqrt (2 / x + 2) = 3 / 2) :
    x = 8 := by
  have h1 : 2 / x + 2 ≥ 0 := by
    by_contra h2
    push_neg at h2
    have h3 : Real.sqrt (2 / x + 2) = 0 := by
      rw [Real.sqrt_eq_zero'.mpr (by linarith)]
      all_goals nlinarith
    rw [h3] at h
    norm_num at h 
    all_goals norm_num at h
    all_goals nlinarith
    all_goals norm_num at h 
    all_goals nlinarith
  have h2 : (2 / x + 2) = (3 / 2) ^ 2 := by
    calc
      (2 / x + 2) = (Real.sqrt (2 / x + 2)) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith [h1]
      _ = (3 / 2) ^ 2 := by 
        rw [h]
    all_goals nlinarith
  have h3 : 2 / x + 2 = 9 / 4 := by
    nlinarith
  have h4 : 2 / x = 1 / 4 := by
    linarith
  have h5 : x = 8 := by 
    have h6 : x ≠ 0 := hx
    field_simp at h4
    nlinarith
  exact h5