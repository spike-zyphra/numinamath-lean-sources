import Mathlib

theorem algebra_159418 (a b : ℝ) (h : ∃ x1 x2 : ℝ, x1 ∈ Set.Ioo 0 1 ∧ x2 ∈ Set.Ioi 1 ∧
    x1^3 + a * x1^2 + b * x1 - a - b - 1 = 0 ∧ x2^3 + a * x2^2 + b * x2 - a - b - 1 = 0) :
    0 < (2 * a + b + 1) / (a + 1) ∧ (2 * a + b + 1) / (a + 1) < 2 := by
  rcases h with ⟨x1, x2, hx1, hx2, h1, h2⟩
  rcases hx1 with ⟨hx10, hx11⟩
  have hx21 : x2 > 1 := by
    simpa using hx2
  have h_eq1 : (x1 - 1) * (x1 ^ 2 + (1 + a) * x1 + (1 + a + b)) = 0 := by
    nlinarith
  have h_eq2 : (x2 - 1) * (x2 ^ 2 + (1 + a) * x2 + (1 + a + b)) = 0 := by
    nlinarith
  have h21 : x1 ^ 2 + (1 + a) * x1 + (1 + a + b) = 0 := by
    have h21 : x1 - 1 ≠ 0 := by
      nlinarith
    have : x1 ^ 2 + (1 + a) * x1 + (1 + a + b) = 0 := by
      apply (mul_left_inj' h21).mp
      linarith
    assumption
  have h22 : x2 ^ 2 + (1 + a) * x2 + (1 + a + b) = 0 := by
    have h22 : x2 - 1 ≠ 0 := by
      nlinarith
    have : x2 ^ 2 + (1 + a) * x2 + (1 + a + b) = 0 := by
      apply (mul_left_inj' h22).mp
      linarith
    assumption
  have h3 : (1:ℝ) ^ 2 + (1 + a) * (1:ℝ) + (1 + a + b) < 0 := by
    nlinarith [sq_pos_of_pos (show 0 < (x2 - 1) by nlinarith), sq_pos_of_pos (show 0 < (1 - x1) by nlinarith), sq_nonneg (x2 - 1), sq_nonneg (x1 - 1), mul_pos (show 0 < (x2 - 1) by nlinarith) (show 0 < (1 - x1) by nlinarith)]
  have h4 : (0:ℝ) ^ 2 + (1 + a) * (0:ℝ) + (1 + a + b) > 0 := by
    nlinarith [sq_pos_of_pos (show 0 < x1 by linarith), sq_pos_of_pos (show 0 < (x2 - 1) by nlinarith), sq_nonneg (x1 - 0), sq_nonneg (x2 - 1), mul_pos (show 0 < x1 by linarith) (show 0 < (x2 - 1) by nlinarith)]
  have ha1 : a + 1 < 0 := by
    nlinarith
  have h5 : 2 * a + b + 1 < 0 := by
    nlinarith
  have h7 : 0 < (2 * a + b + 1) / (a + 1) := by
    apply div_pos_of_neg_of_neg
    all_goals linarith
  have h8 : (2 * a + b + 1) / (a + 1) < 2 := by
    have h9 : a + 1 < 0 := ha1
    apply (div_lt_iff_of_neg' (by linarith)).mpr
    nlinarith
  constructor
  · exact h7
  · exact h8