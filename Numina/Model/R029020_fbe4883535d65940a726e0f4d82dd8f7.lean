import Mathlib

theorem algebra_213445 {a : ℝ} (ha : a ≠ 0) (h : a^2/3-3/a^2=4) :
    (a^12-729)/(27*a^6) = 76 := by
  have h1 : a^2/3-3/a^2=4 := h
  have eq1 : a ^ 4 - 9 = 12 * a^2 := by
    have eq2 : a ^ 2 / 3 - 3 / a ^ 2 = 4 := h
    field_simp [ha] at eq2 ⊢
    nlinarith [sq_pos_of_ne_zero ha, sq_nonneg (a ^ 2 - 3), sq_nonneg (a^2), sq_nonneg (a^2 * (a))]
  have h2 : a ^ 4 = 12 * a ^ 2 + 9 := by linarith
  have eq3 : a^12 - 729 = 76 * 27 * a^6 := by
    have eq4 : a^12 - 729 = (a^4) ^ 3 - (9: ℝ) ^ 3 := by
      ring_nf
    rw [eq4]
    have eq5 : (a ^ 4) ^ 3 - (9 : ℝ) ^ 3 = (a^4 - 9) * ((a^4) ^ 2 + (a ^ 4) * (9) + (9 : ℝ) ^ 2) := by
      ring
    rw [eq5]
    rw [show a^4 - 9 = 12 * a^2 by linarith [eq1]]
    have eq6 : (a^4) ^ 2 + (a ^ 4) * (9) + (9 : ℝ) ^ 2 = a^8 + 9 * a^4 + 81 := by
      ring_nf
    rw [eq6]
    nlinarith [sq_pos_of_ne_zero ha, sq_nonneg (a^2 - 3), sq_nonneg (a^4 - 12 * a^2 - 9), sq_nonneg (a^2), sq_nonneg (a^6 * a^2), sq_pos_of_ne_zero ha, sq_nonneg (a^2 * a^2 - 9), sq_nonneg (a^2 - 1), sq_nonneg ((a^2 + 3) ^ 2), sq_nonneg ((a^2 - 3) ^ 2)]
  -- Use eq3 to form the final result.
  have eq4 : a^12 - 729 = 76 * (27 * a^6) := by
    have eq5 : a^12 - 729 = 76 * 27 * a^6 := eq3
    linarith
  have eq3' : (a^12 - 729) / (27 * a^6) = 76 := by
    have eq3'' : (a^12 - 729) = 76 * (27 * a^6) := eq4
    field_simp [ha]
    linarith
  exact eq3'