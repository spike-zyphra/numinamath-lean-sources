import Mathlib

theorem algebra_288126 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : 1 / a = 1 / (b * c) + 1 / (a * c)) (h2 : 1 / b = 1 / (a * c) + 1 / (a * b))
    (h3 : 1 / c = 1 / (a * b) + 1 / (a * c)) :
    1 / (a + 1) + 1 / (b + 1) + 1 / (c + 1) = 1 := by

  have eq1 : b * c = a + b := by
    have h11 : a ≠ 0 := by nlinarith
    have h12 : b * c ≠ 0 := by nlinarith
    have h13 : a * c ≠ 0 := by nlinarith
    field_simp at h1
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have eq2 : a * c = b + c := by
    have h11 : a ≠ 0 := by nlinarith
    have h12 : b * c ≠ 0 := by nlinarith
    have h13 : a * c ≠ 0 := by nlinarith
    field_simp at h2
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have eq3 : a * b = b + c := by
    have h11 : a ≠ 0 := by nlinarith
    have h12 : b * c ≠ 0 := by nlinarith
    have h13 : a * c ≠ 0 := by nlinarith
    field_simp at h3
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have eq4 : c = b := by
    nlinarith

  have eq5 : a = 2 := by
    have eq6 : c = b := eq4
    rw [eq6] at eq2
    nlinarith [sq_pos_of_pos hb]

  have eq6 : b = 2 := by
    rw [eq4] at eq1
    rw [eq5] at eq1
    nlinarith [sq_pos_of_pos hb]

  have eq7 : c = 2 := by
    linarith [eq4, eq6]

  rw [eq5, eq6, eq7]
  norm_num