import Mathlib

theorem algebra_287434 {h r : ℝ}
    (hh : 3 * 60 / h - 3 * 60 / (4 * h) = 27)
    (hr : 6 * 60 / r - 6 * 60 / (4 * r) = 120) : 
    h = 5 ∧ r = 2.25 := by
  have h1 : h ≠ 0 := by
    by_contra h2
    rw [h2] at hh
    norm_num at hh
  have r1 : r ≠ 0 := by
    by_contra r2
    rw [r2] at hr
    norm_num at hr
  have eq1 : h = 5 := by
    field_simp [h1] at hh
    nlinarith [sq_pos_of_ne_zero (show h ≠ 0 by assumption)]
  have eq2 : r = 2.25 := by
    field_simp [r1] at hr
    norm_num at hr
    nlinarith [sq_pos_of_ne_zero (show r ≠ 0 by assumption)]
  exact ⟨eq1, eq2⟩