import Mathlib

theorem inequalities_63224 (a b c : ℝ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (hroots : a + b + c = 6 ∧ a * b + b * c + c * a = 9) (hord : a < b ∧ b < c) :
    0 < a ∧ a < 1 ∧ 1 < b ∧ b < 3 ∧ 3 < c ∧ c < 4 := by
  rcases hroots with ⟨h1, h2⟩
  rcases hord with ⟨hord1, hord2⟩
  constructor
  · -- Show 0 < a
    nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by
      intro h
      apply ha
      linarith), sq_pos_of_ne_zero (show (b - c) ≠ 0 by
      intro h
      apply hb
      linarith), sq_pos_of_ne_zero (show (a - c) ≠ 0 by
      intro h
      apply hc
      linarith), sq_nonneg (a - 1), sq_nonneg (b - 3), sq_nonneg (c - 4)]
  constructor
  · -- Show a < 1
    nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by
      intro h
      apply ha
      linarith), sq_pos_of_ne_zero (show (b - c) ≠ 0 by
      intro h
      apply hb
      linarith), sq_pos_of_ne_zero (show (a - c) ≠ 0 by
      intro h
      apply hc
      linarith), sq_nonneg (a - 1), sq_nonneg (b - 3), sq_nonneg (c - 4)]
  constructor
  · -- Show 1 < b
    nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by
      intro h
      apply ha
      linarith), sq_pos_of_ne_zero (show (b - c) ≠ 0 by
      intro h
      apply hb
      linarith), sq_pos_of_ne_zero (show (a - c) ≠ 0 by
      intro h
      apply hc
      linarith), sq_nonneg (a - 1), sq_nonneg (b - 3), sq_nonneg (c - 4)]
  constructor
  · -- Show b < 3
    nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by
      intro h
      apply ha
      linarith), sq_pos_of_ne_zero (show (b - c) ≠ 0 by
      intro h
      apply hb
      linarith), sq_pos_of_ne_zero (show (a - c) ≠ 0 by
      intro h
      apply hc
      linarith), sq_nonneg (a - 1), sq_nonneg (b - 3), sq_nonneg (c - 4)]
  constructor
  · -- Show 3 < c
    nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by
      intro h
      apply ha
      linarith), sq_pos_of_ne_zero (show (b - c) ≠ 0 by
      intro h
      apply hb
      linarith), sq_pos_of_ne_zero (show (a - c) ≠ 0 by
      intro h
      apply hc
      linarith), sq_nonneg (a - 1), sq_nonneg (b - 3), sq_nonneg (c - 4)]
  · -- Show c < 4
    nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by
      intro h
      apply ha
      linarith), sq_pos_of_ne_zero (show (b - c) ≠ 0 by
      intro h
      apply hb
      linarith), sq_pos_of_ne_zero (show (a - c) ≠ 0 by
      intro h
      apply hc
      linarith), sq_nonneg (a - 1), sq_nonneg (b - 3), sq_nonneg (c - 4)]