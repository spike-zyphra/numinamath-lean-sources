import Mathlib

theorem inequalities_41827 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a * b + b * c + a * c = 0) :
    (a + b + c) > 0 ∧ (1 / (a + b) + 1 / (b + c) + 1 / (a + c)) > 0 ∨
    (a + b + c) < 0 ∧ (1 / (a + b) + 1 / (b + c) + 1 / (a + c)) < 0 := by
  by_cases h1 : a + b + c > 0
  · -- Assume a + b + c > 0, we need to prove the sum of reciprocals > 0
    have h2 : 1 / (a + b) + 1 / (b + c) + 1 / (a + c) > 0 := by
      have h1a : a + b ≠ 0 := by
        intro h2
        have h3 : a + b = 0 := by linarith
        have h4 : b = -a := by linarith
        rw [show b = -a by linarith] at h
        nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show c ≠ 0 by exact hc)]
      have h1b : b + c ≠ 0 := by
        intro h2
        have h3 : b + c = 0 := by linarith
        have h4 : c = -b := by linarith
        rw [show c = -b by linarith] at h
        nlinarith [sq_pos_of_ne_zero (show b ≠ 0 by exact hb), sq_pos_of_ne_zero (show a ≠ 0 by exact ha)]
      have h1c : a + c ≠ 0 := by
        intro h2
        have h3 : a + c = 0 := by linarith
        have h4 : c = -a := by linarith
        rw [show c = -a by linarith] at h
        nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show b ≠ 0 by exact hb)]
      have h2a : 1 / (a + b) + 1 / (b + c) + 1 / (a + c) = (a^2 + b^2 + c^2) / ((a + b) * (b + c) * (a + c)) := by
        field_simp [(show a + b ≠ 0 by assumption), (show b + c ≠ 0 by assumption), (show a + c ≠ 0 by assumption)]
        ring
        <;> field_simp [(show a + b ≠ 0 by assumption), (show b + c ≠ 0 by assumption), (show a + c ≠ 0 by assumption)]
        <;> ring_nf <;> nlinarith [h]
      rw [h2a]
      have h3a : (a + b) * (b + c) * (a + c) > 0 := by
        nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show b ≠ 0 by exact hb), sq_pos_of_ne_zero (show c ≠ 0 by exact hc), sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
      have h3b : a^2 + b^2 + c^2 > 0 := by
        nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show b ≠ 0 by exact hb), sq_pos_of_ne_zero (show c ≠ 0 by exact hc)]
      apply div_pos
      all_goals nlinarith
    left
    constructor
    · linarith
    · linarith
  · -- Assume a + b + c ≤ 0, prove the sum of reciprocals < 0
    have h1' : a + b + c < 0 := by 
      by_contra h2
      push_neg at h2
      have : a + b + c = 0 := by linarith
      nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show b ≠ 0 by exact hb), sq_pos_of_ne_zero (show c ≠ 0 by exact hc), sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    have h2 : 1 / (a + b) + 1 / (b + c) + 1 / (a + c) < 0 := by
      have h1a : a + b ≠ 0 := by
        intro h2
        have h3 : a + b = 0 := by linarith
        have h4 : b = -a := by linarith
        rw [show b = -a by linarith] at h
        nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show c ≠ 0 by exact hc)]
      have h1b : b + c ≠ 0 := by
        intro h2
        have h3 : b + c = 0 := by linarith
        have h4 : c = -b := by linarith
        rw [show c = -b by linarith] at h
        nlinarith [sq_pos_of_ne_zero (show b ≠ 0 by exact hb), sq_pos_of_ne_zero (show a ≠ 0 by exact ha)]
      have h1c : a + c ≠ 0 := by
        intro h2
        have h3 : a + c = 0 := by linarith
        have h4 : c = -a := by linarith
        rw [show c = -a by linarith] at h
        nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show b ≠ 0 by exact hb)]
      have h2a : 1 / (a + b) + 1 / (b + c) + 1 / (a + c) = (a^2 + b^2 + c^2) / ((a + b) * (b + c) * (a + c)) := by
        field_simp [(show a + b ≠ 0 by assumption), (show b + c ≠ 0 by assumption), (show a + c ≠ 0 by assumption)]
        ring
        <;> field_simp [(show a + b ≠ 0 by assumption), (show b + c ≠ 0 by assumption), (show a + c ≠ 0 by assumption)]
        <;> ring_nf <;> nlinarith [h]
      rw [h2a]
      have h3a : (a + b) * (b + c) * (a + c) < 0 := by
        nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show b ≠ 0 by exact hb), sq_pos_of_ne_zero (show c ≠ 0 by exact hc), sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
      have h3b : a^2 + b^2 + c^2 > 0 := by
        nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show b ≠ 0 by exact hb), sq_pos_of_ne_zero (show c ≠ 0 by exact hc)]
      apply div_neg_of_pos_of_neg
      all_goals nlinarith
    right
    constructor
    · linarith
    · linarith