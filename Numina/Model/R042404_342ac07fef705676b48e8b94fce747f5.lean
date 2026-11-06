import Mathlib

theorem inequalities_186572 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    a ^ 4 + b ^ 4 > a ^ 3 * b + a * b ^ 3 ∧ a ^ 5 + b ^ 5 > a ^ 3 * b ^ 2 + a ^ 2 * b ^ 3 := by

  constructor
  · -- Prove that $a^4 + b^4 > a^3 * b + a * b^3$
    have h1 : a ^ 4 + b ^ 4 - (a ^ 3 * b + a * b ^ 3) > 0 := by
      have h1 : (a - b) ^ 2 > 0 := by
        apply sq_pos_of_ne_zero
        intro h
        apply hab
        linarith
      have h2 : a^2 + a * b + b^2 > 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb, sq_pos_of_pos ha, sq_pos_of_pos hb]
      have h3 : (a - b) ^ 2 * (a^2 + a * b + b^2) > 0 := by
        apply mul_pos
        linarith
        linarith
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_pos_of_ne_zero (show (a - b) ≠ 0 by
        intro h
        apply hab
        linarith
      ), mul_pos ha hb, pow_pos ha 2, pow_pos ha 3, pow_pos ha 4, pow_pos hb 2, pow_pos hb 3, pow_pos hb 4, sq_nonneg (a - b)]
    nlinarith
  · -- Prove that $a^5 + b^5 > a^3 * b^2 + a^2 * b^3$
    have h2 : a^5 + b^5 - (a^3 * b^2 + a^2 * b^3) > 0 := by
      have h1 : (a - b) ^ 2 > 0 := by
        apply sq_pos_of_ne_zero
        intro h
        apply hab
        linarith
      have h2 : a + b > 0 := by
        linarith
      have h3 : a^2 + a * b + b^2 > 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb, sq_pos_of_pos ha, sq_pos_of_pos hb]
      have h4 : (a - b) ^ 2 * (a + b) * (a^2 + a * b + b^2) > 0 := by
        apply mul_pos
        apply mul_pos
        linarith
        linarith
        linarith
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_pos_of_ne_zero (show (a - b) ≠ 0 by
        intro h
        apply hab
        linarith
      ), mul_pos ha hb, pow_pos ha 2, pow_pos ha 3, pow_pos ha 4, pow_pos ha 5, pow_pos hb 2, pow_pos hb 3, pow_pos hb 4, pow_pos hb 5, sq_nonneg (a - b)]
    nlinarith