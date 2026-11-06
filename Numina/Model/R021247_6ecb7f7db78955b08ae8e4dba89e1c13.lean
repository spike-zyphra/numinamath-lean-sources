import Mathlib

theorem algebra_4529 (v s : ℝ) (h1 : 0 < v) (h2 : 0 < s) (h3 : 80 / (v + s) + 48 / (v - s) = 9) (h4 : 60 / (v + s) + 96 / (v - s) = 12) :
    v = 14 + 1 / 21 := by
  have h5 : v + s ≠ 0 := by
    nlinarith
  have h6 : v - s ≠ 0 := by
    by_contra h
    have h7 : s = v := by linarith
    rw [show s = v by linarith] at h3 h4
    field_simp [(show v + v ≠ 0 by nlinarith)] at h3 h4
    nlinarith
  have eq1 : 80 * (v - s) + 48 * (v + s) = 9 * ((v + s) * (v - s)) := by
    have h5' : v + s ≠ 0 := h5
    have h6' : v - s ≠ 0 := h6
    field_simp [h5', h6'] at h3 ⊢
    nlinarith
  have eq2 : 60 * (v - s) + 96 * (v + s) = 12 * ((v + s) * (v - s)) := by
    have h5' : v + s ≠ 0 := h5
    have h6' : v - s ≠ 0 := h6
    field_simp [h5', h6'] at h4 ⊢
    nlinarith
  have eq3 : 9 * v ^ 2 - 9 * s ^ 2 - 128 * v + 32 * s = 0 := by
    nlinarith [eq1]
  have eq4 : 12 * v ^ 2 - 12 * s ^ 2 - 156 * v - 36 * s = 0 := by
    nlinarith [eq2]
  have eq5 : 11 * v = 59 * s := by
    nlinarith [eq3, eq4]
  have eq6 : s = 55 / 21 := by
    have eq7 : v ^ 2 - s ^ 2 - 13 * v - 3 * s = 0 := by
      nlinarith [eq4]
    have eq8 : v = 59 / 11 * s := by
      linarith [eq5]
    rw [eq8] at eq7
    nlinarith [sq_pos_of_pos h1, sq_pos_of_pos h2]
  have eq7 : v = 295 / 21 := by
    have eq8 : 11 * v = 59 * s := by
      linarith [eq5]
    rw [show s = 55 / 21 by linarith [eq6]] at eq8
    linarith
  linarith [eq7]