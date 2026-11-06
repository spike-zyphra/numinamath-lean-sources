import Mathlib

open Real

theorem inequalities_262573 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    (a + b) / 2 < 2 * (a ^ 2 + a * b + b ^ 2) / (3 * (a + b)) ∧
    2 * (a ^ 2 + a * b + b ^ 2) / (3 * (a + b)) < sqrt ((a ^ 2 + b ^ 2) / 2) := by
  constructor
  · -- First part: (a + b) / 2 < 2 * (a ^ 2 + a * b + b ^ 2) / (3 * (a + b))
    have h1 : 0 < a + b := by linarith
    have h2 : (a + b) / 2 < 2 * (a ^ 2 + a * b + b ^ 2) / (3 * (a + b)) := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by
        intro h
        apply hab
        linarith), sq_nonneg (a - b), sq_nonneg (a + b)]
    exact h2
  · -- Second part: 2 * (a ^ 2 + a * b + b ^ 2) / (3 * (a + b)) < sqrt ((a ^ 2 + b ^ 2) / 2)
    have h1 : 0 < a + b := by linarith
    have h2 : (2 * (a ^ 2 + a * b + b ^ 2) / (3 * (a + b)) ) < sqrt ((a ^ 2 + b ^ 2) / 2) := by
      have h3 : (2 * (a ^ 2 + a * b + b ^ 2) / (3 * (a + b)) ) ≥ 0 := by
        apply div_nonneg
        · -- Numerator is non-negative
          nlinarith [sq_nonneg (a - b), mul_pos ha hb]
        · -- Denominator is non-negative
          nlinarith [show 0 < a by linarith, show 0 < b by linarith]
      have h4 : (sqrt ((a ^ 2 + b ^ 2) / 2) ) ≥ 0 := by positivity
      have h5 : (2 * (a ^ 2 + a * b + b ^ 2) / (3 * (a + b)) ) ^ 2 < (sqrt ((a ^ 2 + b ^ 2) / 2) ) ^ 2 := by
        have h6 : (sqrt ((a ^ 2 + b ^ 2) / 2) ) ^ 2 = (a ^ 2 + b ^ 2) / 2 := by
          rw [Real.sq_sqrt]
          positivity
        have h7 : (2 * (a ^ 2 + a * b + b ^ 2) / (3 * (a + b)) ) ^ 2 < (a ^ 2 + b ^ 2) / 2 := by
          have h8 : 0 < a + b := h1
          have h9 : 0 < (3 * (a + b) ) ^ 2 := by positivity
          have h10 : (2 * (a ^ 2 + a * b + b ^ 2) / (3 * (a + b)) ) ^ 2 = 4 * (a ^ 2 + a * b + b ^ 2) ^ 2 / (9 * (a + b) ^ 2) := by
            field_simp
            <;> ring
          rw [h10]
          have h11 : 4 * (a ^ 2 + a * b + b ^ 2) ^ 2 / (9 * (a + b) ^ 2) < (a ^ 2 + b ^ 2) / 2 := by
            apply (div_lt_div_iff (by positivity) (by positivity)).mpr
            nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by
              intro h
              apply hab
              linarith), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb, sq_nonneg (a * b), sq_nonneg (a^2 - b^2)]
          linarith [h11, h6]
        nlinarith [h7, h6]
      nlinarith [Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2), h3, h4, h5]
    exact h2