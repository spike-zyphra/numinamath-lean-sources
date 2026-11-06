import Mathlib

theorem algebra_206395 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : 1 / (a + b + c) = 1 / a - 6) (h2 : 1 / (a + b + c) = 1 / b - 1)
    (h3 : 1 / (a + b + c) = 1 / c / 2) :
    1 / (a + b) = 4 / 3 := by
  have h4 : a + b + c ≠ 0 := by
    linarith
  have h5 : a ≠ 0 := by linarith
  have h6 : b ≠ 0 := by linarith
  have h7 : c ≠ 0 := by linarith
  field_simp [h4, h5, h6, h7] at h1 h2 h3
  have h8 : a + b - c = 0 := by
    nlinarith [h3]
  have h9 : c = a + b := by linarith [h8]
  rw [show c = a + b by linarith [h8]] at h1 h2
  have h10 : a + b > 0 := by
    nlinarith
  have h12 : a + b = 3 / 4 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos (show 0 < a + b by nlinarith), sq_nonneg (a - b), sq_nonneg (a + b - 1)]
  have h14 : 1 / (a + b) = 4 / 3 := by
    rw [show a + b = 3 / 4 by linarith]
    field_simp
  exact h14