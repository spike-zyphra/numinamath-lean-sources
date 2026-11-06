import Mathlib

theorem algebra_297112 {x : ℝ} (hx : x < 0) : x * Real.sqrt (-1 / x) = -Real.sqrt (-x) := by

  have h1 : -x > 0 := by linarith
  have h2 : -1 / x > 0 := by
    have h3 : x < 0 := hx
    have h4 : -x > 0 := by linarith
    have h5 : -1 / x = 1 / (-x) := by
      field_simp [(show x ≠ 0 by linarith)]
    rw [h5]
    apply div_pos
    norm_num
    all_goals linarith

  have h3 : Real.sqrt (-1 / x) = 1 / Real.sqrt (-x) := by
    have h5 : Real.sqrt (-1 / x) = Real.sqrt (1 / (-x)) := by
      have h6 : (1 / (-x) : ℝ) = -1 / x := by
        field_simp [(show x ≠ 0 by linarith)]
      rw [h6]
    have h6 : Real.sqrt (1 / (-x)) = 1 / Real.sqrt (-x) := by
      rw [Real.sqrt_div (by norm_num)]
      <;> field_simp [Real.sqrt_nonneg (-x), Real.sqrt_pos.mpr h1]
      all_goals nlinarith [Real.sqrt_pos.mpr h1]

    rw [h5, h6]

  rw [h3]

  have h4 : Real.sqrt (-x) > 0 := by
    apply Real.sqrt_pos.2
    linarith

  field_simp [(show Real.sqrt (-x) ≠ 0 by nlinarith [Real.sqrt_nonneg (-x), h4])]
  <;> nlinarith [Real.sqrt_nonneg (-x), Real.sq_sqrt (show (0 : ℝ) ≤ -x by linarith)]