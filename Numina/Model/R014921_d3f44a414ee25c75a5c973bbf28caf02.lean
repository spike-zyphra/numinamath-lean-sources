import Mathlib

open Real

theorem inequalities_258663 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a^2 + b^2 = 1 / 2) :
    4 ≤ 1 / (1 - a) + 1 / (1 - b) ∧
    (4 = 1 / (1 - a) + 1 / (1 - b) ↔ a = b) := by
  have ha1 : a < 1 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]
  have hb1 : b < 1 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]

  constructor
  · -- Show that 4 ≤ 1/(1-a) + 1/(1-b)
    have h1 : (1 - a) * (1 - b) > 0 := by
      apply mul_pos
      linarith
      linarith
    have h2 : 2 - a - b ≥ 4 * (1 - a) * (1 - b) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), 
          h, mul_pos ha hb]
    have h3 : 1 / (1 - a) + 1 / (1 - b) - 4 ≥ 0 := by
      have h4 : 0 < (1 - a) := by linarith
      have h5 : 0 < (1 - b) := by linarith
      have h6 : (1 - a) * (1 - b) > 0 := by
        nlinarith
      have h7 : (1 / (1 - a) + 1 / (1 - b) - 4) = ( ( (1 - b) + (1 - a) ) - 4 * ((1 - a) * (1 - b)) ) / ((1 - a) * (1 - b)) := by
        field_simp
        <;> ring_nf
        <;> field_simp
        <;> ring
      rw [h7]
      apply div_nonneg
      nlinarith
      positivity
    linarith
  · -- Show that 4 = 1/(1-a) + 1/(1-b) ↔ a = b
    constructor
    · -- Assume 4 = 1/(1 - a) + 1/(1 - b), prove a = b
      intro heq
      have h1 : (1 - a) * (1 - b) > 0 := by
        apply mul_pos
        linarith
        linarith
      have eq1 : 4 * ((1 - a) * (1 - b)) = (1 - b) + (1 - a) := by
        field_simp [(show (1 - a : ℝ) ≠ 0 by linarith), (show (1 - b : ℝ) ≠ 0 by linarith)] at heq ⊢
        nlinarith
        all_goals nlinarith
      have hsq : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1), h, mul_pos ha hb]
      have hab : a = b := by
        nlinarith
      exact hab
    · -- Assume a = b, prove 4 = 1/(1 - a) + 1/(1 - b)
      intro h_eq
      have ha2 : a = b := by
        linarith
      have h2 : a < 1 := by
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_nonneg (a - 1/2), sq_nonneg (b - 1/2)]
      have h3 : b < 1 := by
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_nonneg (a - 1/2), sq_nonneg (b - 1/2)]
      have h4 : a = 1 / 2 := by
        have h6 : a = b := by
          linarith [h_eq]
        have h7 : 2 * a ^ 2 = 1 / 2 := by
          have h8 : b ^ 2 = a ^ 2 := by
            rw [show b = a by linarith [h_eq]]
          nlinarith [h, sq_nonneg (a - b), sq_nonneg (a + b - 1)]
        have h11 : a ^ 2 = 1 / 4 := by
          nlinarith
        have h5 : a > 0 := by
          nlinarith
        have h10 : a = 1 / 2 := by
          nlinarith
        exact h10
      rw [show b = a by linarith [h_eq], h4]
      norm_num
      <;> field_simp [(show (1 - (1 / 2) : ℝ) ≠ 0 by norm_num)]
      <;> norm_num
      <;> linarith