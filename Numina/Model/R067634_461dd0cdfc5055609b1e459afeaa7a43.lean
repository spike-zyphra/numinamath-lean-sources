import Mathlib

theorem algebra_2622 (a b : ℝ) (ha : 0 < a) (hb : a < b) (h1 : b < 1) (h2 : a + b = 1) :
    a < (1 / 2) ∧ (1 / 2) < a ^ 2 + b ^ 2 ∧ a ^ 2 + b ^ 2 < b := by
  have h3 : a < 1 / 2 := by linarith [h2, h1, hb]
  have h4 : 1 / 2 < a ^ 2 + b ^ 2 := by 
    have h5 : b = 1 - a := by linarith
    rw [h5]
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a - 1), sq_nonneg (a - b), sq_pos_of_pos (show 0 < 1 - a by nlinarith), sq_pos_of_pos ha]
  have h6 : a ^ 2 + b ^ 2 < b := by 
    have h5 : b = 1 - a := by linarith
    rw [h5]
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a - 1), sq_nonneg (a - b), sq_pos_of_pos (show 0 < 1 - a by nlinarith), sq_pos_of_pos ha]
  exact ⟨h3, h4, h6⟩