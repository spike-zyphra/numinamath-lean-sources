import Mathlib

theorem algebra_125885 (a b : ℝ) (h : ∃ x1 x2, x1^2 + (a + 1) * x1 + a + b + 1 = 0 ∧ x2^2 + (a + 1) * x2 + a + b + 1 = 0 ∧ 0 < x1 ∧ x1 < 1 ∧ x2 > 1) :
    b / a ∈ Set.Ioo (-2) (-1 / 2) := by
  rcases h with ⟨x1, x2, hx1, hx2, hx10, hx11, hx21⟩
  have ha1 : a < 0 := by
    nlinarith [sq_pos_of_pos (show (x1) > 0 by linarith), sq_pos_of_pos (show (x2) > 0 by nlinarith)]
  have h6 : b / a < -1 / 2 := by
    apply (div_lt_iff_of_neg' (by linarith)).mpr
    nlinarith [mul_pos (show 0 < x1 by linarith) (show 0 < x2 by nlinarith), sq_pos_of_pos (show 0 < x1 by linarith), sq_pos_of_pos (show 0 < x2 by nlinarith), sq_pos_of_pos (show (0 : ℝ) < x1 by linarith), sq_pos_of_pos (show (0 : ℝ) < x2 by nlinarith)]
  have h7 : b / a > -2 := by
    apply (lt_div_iff_of_neg' (by linarith)).mpr
    nlinarith [mul_pos (show 0 < x1 by linarith) (show 0 < x2 by nlinarith), sq_pos_of_pos (show 0 < x1 by linarith), sq_pos_of_pos (show 0 < x2 by nlinarith), sq_pos_of_pos (show (0 : ℝ) < x1 by linarith), sq_pos_of_pos (show (0 : ℝ) < x2 by nlinarith)]
  exact ⟨by linarith [h7], by linarith [h6]⟩