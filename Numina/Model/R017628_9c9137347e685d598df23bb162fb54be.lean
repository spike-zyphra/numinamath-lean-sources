import Mathlib

theorem algebra_319664 (x : ℝ) (hx : 0 < x ∧ x < 1) :
    Real.sqrt ((x - 1 / x)^2 + 4) - Real.sqrt ((x + 1 / x)^2 - 4) = 2 * x := by
  have h1 : 0 < x := hx.1
  have h2 : x < 1 := hx.2
  have h3 : Real.sqrt ((x - 1 / x) ^ 2 + 4) = x + 1 / x := by
    have h3_1 : (x - 1 / x) ^ 2 + 4 = (x + 1 / x) ^ 2 := by
      field_simp
      <;> nlinarith
    rw [h3_1]
    have h3_2 : 0 ≤ x + 1 / x := by
      have hx1 : 0 < x := h1
      have hx2 : 0 < 1 / x := by
        apply div_pos
        norm_num
        all_goals linarith
      have h3_2 : x + 1 / x > 0 := by linarith [h1, hx2]
      linarith [h3_2]
    rw [Real.sqrt_sq (show 0 ≤ x + 1 / x by linarith)]
  have h4 : Real.sqrt ((x + 1 / x) ^ 2 - 4) = (1 / x - x) := by
    have h4_1 : (x + 1 / x) ^ 2 - 4 = (x - 1 / x) ^ 2 := by
      field_simp
      <;> nlinarith
    rw [h4_1]
    have h4_2 : Real.sqrt ((x - 1 / x) ^ 2) = |x - 1 / x| := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h4_2]
    have h4_3 : x - 1 / x < 0 := by
      have h1' : 0 < x := h1
      have h2' : x < 1 := h2
      have h3' : 1 / x > 1 := by
        have : x * (1 / x) = 1 := by
          field_simp
        have h4' : (x) * (1 / x) = 1 := by
          field_simp
        have h5' : x < 1 := h2
        have h6' : 1 / x > 1 := by
          apply (lt_div_iff' (by linarith)).mpr
          nlinarith
        linarith
      have h4_4 : x - 1 / x < 0 := by linarith [h3']
      linarith
    have h4_4 : |x - 1 / x| = (1 / x - x) := by
      have h4_3' : x - 1 / x < 0 := h4_3
      rw [abs_of_neg (show x - 1 / x < 0 by linarith)]
      all_goals linarith
    rw [h4_4]
  rw [h3, h4]
  have h5 : x + 1 / x - (1 / x - x) = 2 * x := by
    field_simp
    <;> nlinarith
  linarith [h5]