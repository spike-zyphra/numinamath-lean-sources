import Mathlib

theorem algebra_236036 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : b * (c + a) = (a * (b + c) + c * (a + b)) / 2) (hb2 : b = 2019 / 2020) :
    (1 / a + 1 / b + 1 / c) / 3 = 2020 / 2019 := by

  have eq1 : 2 * b * (c + a) = a * (b + c) + c * (a + b) := by
    linarith [h]

  have eq2 : b * (c + a) = 2 * a * c := by 
    linarith [eq1]

  have eq3 : 1 / a + 1 / b + 1 / c = 3 / b := by
    have eq4 : 1 / a + 1 / b + 1 / c = (b * c + a * c + a * b) / (a * b * c) := by
      field_simp [ha, hb, hc]
      ring
    have eq5 : b * c + a * c + a * b = 3 * a * c := by
      have eq6 : b * (c + a) = 2 * a * c := eq2
      have eq7 : b * c + a * b = 2 * a * c := by
        linarith [eq6]
      linarith [eq7]
    have eq8 : (b * c + a * c + a * b) / (a * b * c) = 3 / b := by
      have eq9 : a * b * c ≠ 0 := by
        apply mul_ne_zero
        apply mul_ne_zero
        · exact ha
        · exact hb
        · exact hc
      field_simp [eq9, hb]
      <;> nlinarith [eq5, sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc]
    rw [eq4, eq8]

  have eq4 : (1 / a + 1 / b + 1 / c) / 3 = 1 / b := by
    rw [eq3]
    field_simp [hb]
    <;> nlinarith [sq_pos_of_ne_zero hb]

  rw [eq4, hb2]
  all_goals norm_num