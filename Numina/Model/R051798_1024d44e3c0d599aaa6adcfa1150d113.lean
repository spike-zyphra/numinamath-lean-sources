import Mathlib

theorem algebra_322323 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a < 5) (h2 : a^2 - a - 2 * b - 2 * c = 0) (h3 : a + 2 * b - 2 * c + 3 = 0) :
    b < a ∧ a < c := by
  have eq_b : b = (a^2 - 2 * a - 3) / 4 := by 
    nlinarith [h2, h3]
  have eq_c : c = (a^2 + 3) / 4 := by 
    nlinarith [h2, h3, eq_b]
  have h4 : b < a := by 
    rw [eq_b]
    nlinarith [sq_nonneg (a - 3), h1]
  have h5 : a < c := by 
    rw [eq_c]
    nlinarith [sq_pos_of_pos (show 0 < a by linarith), sq_nonneg (a - 3)]
  constructor 
  · linarith [h4]
  · linarith [h5]