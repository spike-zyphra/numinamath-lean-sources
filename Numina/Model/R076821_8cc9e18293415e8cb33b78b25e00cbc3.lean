import Mathlib

theorem algebra_297852 {a b : ℝ} (ha : a^2 + 1 = 3 * a) (hb : b^2 + 1 = 3 * b)
    (hab : a ≠ b) : 1 / a^2 + 1 / b^2 = 7 := by
  have ha1 : a ≠ 0 := by
    rintro rfl
    linarith
  have hb1 : b ≠ 0 := by
    rintro rfl
    linarith
  have h1 : a^2 - 3 * a + 1 = 0 := by linarith
  have h1' : b^2 - 3 * b + 1 = 0 := by linarith
  have h2 : a + b = 3 := by
    have h_sub : a^2 - b^2 - 3 * (a - b) = 0 := by
      nlinarith [h1, h1']
    have h_diff : (a - b) * (a + b - 3) = 0 := by
      linarith [h_sub]
    cases' (mul_eq_zero.1 h_diff) with h3 h4
    · -- Case where $a - b = 0$
      exfalso
      have h4 : a = b := by linarith
      contradiction
    · -- Case where $a + b - 3 = 0$
      linarith
  have h3 : a * b = 1 := by
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne hab), h2, h1, h1']
  have ha2 : a^2 = 3 * a - 1 := by linarith [ha]
  have hb2 : b^2 = 3 * b - 1 := by linarith [hb]
  have h4 : a^2 + b^2 = 7 := by
    nlinarith [h2, ha2, hb2]
  have h4' : (a * b)^2 = 1 := by
    nlinarith [h3]
  have h5 : 1 / a^2 + 1 / b^2 = (a^2 + b^2) / ((a * b) ^ 2) := by
    field_simp [ha1, hb1]
    <;> ring
  rw [h5]
  rw [h4, h4']
  all_goals norm_num