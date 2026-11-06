import Mathlib


lemma lemma_1 (a b : ℝ) (h₀ : a < b) (h₁ : b < 0) :
    b + 1 / a > a + 1 / b := by
  have h2 : a < 0 := by linarith
  have h3 : a * b > 0 := by
    have h6 : a < 0 := by linarith
    have h7 : b < 0 := by linarith
    nlinarith
  have h4 : a * b + 1 > 0 := by
    nlinarith
  have h6 : a ≠ 0 := by
    nlinarith
  have h7 : b ≠ 0 := by
    nlinarith
  have h8 : b + 1 / a > a + 1 / b := by
    have h9 : b + 1 / a - (a + 1 / b) > 0 := by
      have h10 : a * b > 0 := by
        have h6 : a < 0 := by linarith
        have h7 : b < 0 := by linarith
        nlinarith
      have h13 : b + 1 / a - (a + 1 / b) = (b - a) * (1 + 1 / (a * b)) := by
        field_simp [show a ≠ 0 by nlinarith, show b ≠ 0 by nlinarith]
        <;> ring
      rw [h13]
      have h9a : 1 + 1 / (a * b) > 0 := by
        have h9b : 1 / (a * b) > 0 := by
          apply div_pos
          all_goals nlinarith
        linarith
      have h9b : (b - a) > 0 := by
        linarith
      positivity
    linarith
  linarith


theorem inequalities_1731 (a b : ℝ) (h : a < b ∧ b < 0) :
    (b + 1 / a) ^ 2 < (a + 1 / b) ^ 2 := by
  have h₀ : a < b := h.1
  have h₁ : b < 0 := h.2
  have h2 : a < 0 := by nlinarith
  have h3 : b + 1 / a > a + 1 / b := by
    apply lemma_1 a b
    all_goals
    try linarith
  have h4 : a + 1 / b < 0 := by
    have h5 : a < 0 := by linarith
    have h6 : b < 0 := by linarith
    have h7 : 1 / b < 0 := by
      apply div_neg_of_pos_of_neg
      · norm_num
      · linarith
    have h8 : a + 1 / b < 0 := by
      nlinarith
    nlinarith
  have h5 : b + 1 / a < 0 := by
    have h6 : b < 0 := by linarith
    have h7 : 1 / a < 0 := by
      have h8 : a < 0 := by linarith
      apply div_neg_of_pos_of_neg
      · norm_num
      · linarith
    have h8 : b + 1 / a < 0 := by
      nlinarith
    nlinarith
  nlinarith [sq_nonneg (b + 1 / a - (a + 1 / b)), sq_nonneg (b + 1 / a), sq_nonneg (a + 1 / b), sq_pos_of_pos (show 0 < (b - a) by linarith), sq_pos_of_neg (show a < 0 by linarith), sq_pos_of_neg (show b < 0 by linarith)]